use ::libs::{
    colored::Colorize,
    crossbeam::{channel::bounded, select as crossbeam_select, thread::scope},
    divvy::Switch,
    fastrand,
};
use std::{cmp, io};
use tui::{backend::Backend, layout::*, style::*, text::*, widgets::*, Frame, Terminal as Term};

mod completions;
mod events;
mod history;
mod input;
mod outputs;
#[cfg(test)]
mod tests;

use events::*;
use history::History;
use input::InputBuffer;

pub use completions::{Completer, Completion, CompletionType, Completions};
pub use events::Events;
pub use outputs::Outputs;

const SLEEP: std::time::Duration = std::time::Duration::from_millis(5);
const OUTPUTS_LIM: usize = 100;
const NOMOD: KeyModifiers = KeyModifiers::empty();
const SCROLL_LINES: i32 = 5;

// ###### CONFIG ###############################################################
pub type Input = String;
pub type TabId = u64;
pub type Cancelled = Switch;
type DecorationFn = Box<dyn Fn(Input, usize) -> String>;
type EnterFn = Box<dyn FnMut(Input, TabId, Cancelled) -> ConfigUpdate + Send>;
type ConfigBldr = Box<dyn FnMut() -> Config>;

#[derive(Default)]
pub struct ConfigUpdate {
    pub new_title: Option<String>,
    pub new_prompt: Option<String>,
    pub new_completions: Option<Completions>,
    pub add_output: Option<String>,
}

pub struct Config {
    pub title: String,
    /// The prompt before the input.
    pub prompt: String,
    /// Transform the input.
    ///
    /// This can be used to decorate the input using using ansi styling characters.
    /// The input is `(input, cursor_position)`.
    pub decorate_input: DecorationFn,
    /// Run code when `Enter` is pressed.
    ///
    /// The [`ConfigUpdate`] updates the tab's inner config state with any of the fields that are filled.
    pub on_enter_press: EnterFn,
    pub completers: Vec<Box<dyn Completer>>,
}

impl Default for Config {
    fn default() -> Self {
        Self {
            title: "".to_string(),
            prompt: "> ".to_string(),
            decorate_input: Box::new(|s, _| s),
            on_enter_press: Box::new(|s, _, _| ConfigUpdate {
                add_output: Some(s),
                ..Default::default()
            }),
            completers: vec![],
        }
    }
}

// ###### EVENT RESULT #########################################################
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
enum EventResult {
    None,
    Redraw,
    InputChanged,
    Eval,
    Break,
}

// ###### STATE ################################################################
struct TabState {
    id: u64,
    title: String,
    prompt: String,
    input: InputBuffer,
    input_cache: Text<'static>,
    outputs: Outputs,
    completions: Completions,
    decorationfn: DecorationFn,
    history: History,
}

impl TabState {
    fn input_text(&mut self, width: usize) -> Text<'static> {
        if self.input.buffer_changed() {
            let pos = self.input.buf_pos();
            let i = (self.decorationfn)(self.input.buffer(..), pos);
            self.input_cache = convert_coloured_str(&i, width);
            self.input.reset_buf_changed();
        }

        self.input_cache.clone()
    }

    fn update(&mut self, cu: ConfigUpdate) {
        macro_rules! update {
            ($e:expr, $a:ident => $foo:expr) => {{
                if let Some(e) = $e {
                    let $a = e;
                    $foo;
                }
            }};
        }
        let ConfigUpdate {
            new_title,
            new_prompt,
            new_completions,
            add_output,
        } = cu;
        update!(new_title, x => self.title = x);
        update!(new_prompt, x => self.prompt = x);
        update!(new_completions, x => self.completions = x);
        update!(add_output, x => self.outputs.add(x));
    }
}

struct TermState {
    tabs: Vec<TabState>,
    tab_selected: usize,
    draw_help: bool,
    cmpls_drawn: bool,
    config_bldr: ConfigBldr,
}

impl TermState {
    fn tabs_len(&self) -> usize {
        self.tabs.len()
    }

    fn tab_selected(&self) -> usize {
        self.tab_selected
    }

    fn tab_state(&mut self) -> &mut TabState {
        self.tabs.get_mut(self.tab_selected).unwrap()
    }

    fn new_tab(&mut self) {
        let (state, _) = init((self.config_bldr)(), 20);
        self.tabs.push(state);
        self.tab_selected = self.tabs.len().saturating_sub(1);
    }

    fn switch_tab(&mut self) {
        self.tab_selected += 1;
        if self.tab_selected >= self.tabs.len() {
            self.tab_selected = 0;
        }
    }

    fn quit_tab(&mut self) {
        if self.tab_selected < self.tabs.len() {
            self.tabs.remove(self.tab_selected);
        }
        self.switch_tab();
    }
}

// ###### RUNNING ##############################################################
fn init(config: Config, initial_width: u16) -> (TabState, EnterFn) {
    let Config {
        title,
        prompt,
        decorate_input,
        on_enter_press,
        completers,
    } = config;

    let outputs = Outputs::new(initial_width, OUTPUTS_LIM);
    let completions = Completions::new(completers);

    let state = TabState {
        id: fastrand::u64(..),
        title,
        prompt,
        input: InputBuffer::new(),
        input_cache: Text::from(""),
        outputs,
        completions,
        decorationfn: decorate_input,
        history: History::new(),
    };

    (state, on_enter_press)
}

pub fn run<E, B, C>(mut events: E, backend: B, config: C) -> io::Result<Term<B>>
where
    E: Iterator<Item = Event>,
    B: Backend,
    C: FnMut() -> Config + 'static,
{
    let mut terminal = Term::new(backend)?;
    let term = &mut terminal;

    let mut config_bldr = Box::new(config);

    // set up state
    let (state, mut on_enter_press) = init(config_bldr(), term.size()?.width);
    let mut state = TermState {
        tabs: vec![state],
        tab_selected: 0,
        draw_help: true,
        cmpls_drawn: false,
        config_bldr,
    };

    // do an initial draw
    term.clear()?;
    draw(term, &mut state)?;

    // run loop
    while !events_cycle(term, events.by_ref(), &mut on_enter_press, &mut state)? {}

    Ok(terminal)
}

/// This is split from the run loop as it allows us to test a stream of events and check the
/// terminal state.
fn events_cycle<B, E, F>(
    term: &mut Term<B>,
    mut events: E,
    on_enter_press: F,
    state: &mut TermState,
) -> io::Result<bool>
where
    B: Backend,
    E: Iterator<Item = Event>,
    F: FnMut(Input, TabId, Cancelled) -> ConfigUpdate + Send,
{
    // read events
    let r = events
        .by_ref()
        .map(|ev| process_event(ev, state))
        .max()
        .unwrap_or(EventResult::None);

    // handle completions
    let r = match r {
        EventResult::InputChanged => {
            {
                state.cmpls_drawn = false;
                let state = state.tab_state();
                state.completions.request(&state.input);
            }
            EventResult::InputChanged
        }
        EventResult::None if state.tab_state().completions.has() && !state.cmpls_drawn => {
            state.cmpls_drawn = true;
            EventResult::Redraw
        }
        x => x,
    };

    // do action if required
    match r {
        EventResult::Break => return Ok(true),
        EventResult::Eval => {
            eval(term, events, on_enter_press, state);
            draw(term, state)?;
        }
        EventResult::Redraw | EventResult::InputChanged => draw(term, state)?,
        EventResult::None => {
            if !state.tab_state().completions.recv() {
                std::thread::sleep(SLEEP);
            }
        }
    }

    Ok(false)
}

fn process_event(ev: Event, state: &mut TermState) -> EventResult {
    use Event::*;
    use KeyCode::*;
    use KeyModifiers as KM;

    let has_cmpls = state.tab_state().completions.has();

    match ev {
        // ctrl+h toggles help
        Key {
            code: Char('h'),
            mods: KM::CONTROL,
        } => {
            state.draw_help = !state.draw_help;
            EventResult::Redraw
        }
        // ctrl+q quits tab, quits program if all gone
        Key {
            code: Char('q'),
            mods: KM::CONTROL,
        } => {
            state.quit_tab();
            if state.tabs_len() == 0 {
                EventResult::Break
            } else {
                EventResult::Redraw
            }
        }
        // ctrl+t opens a new tab
        Key {
            code: Char('t'),
            mods: KM::CONTROL,
        } => {
            state.new_tab();
            EventResult::Redraw
        }
        // Tab switches tabs
        Key {
            code: Tab,
            mods: NOMOD,
        } => {
            state.switch_tab();
            EventResult::Redraw
        }
        // enter triggers a process
        Key {
            code: Enter,
            mods: NOMOD,
        } => EventResult::Eval,
        // shift+up scrolls the outputs 5 lines up
        Key {
            code: Up,
            mods: KM::SHIFT,
        } => {
            state.tab_state().outputs.scroll(-SCROLL_LINES);
            EventResult::Redraw
        }
        // shift+down scrolls the outputs 5 lines down
        Key {
            code: Down,
            mods: KM::SHIFT,
        } => {
            state.tab_state().outputs.scroll(SCROLL_LINES);
            EventResult::Redraw
        }
        // pgup scrolls the outputs 25 lines up
        Key {
            code: PageUp,
            mods: NOMOD,
        } => {
            state.tab_state().outputs.scroll(SCROLL_LINES * -5);
            EventResult::Redraw
        }
        // pgdown scrolls the outputs 25 lines down
        Key {
            code: PageDown,
            mods: NOMOD,
        } => {
            state.tab_state().outputs.scroll(SCROLL_LINES * 5);
            EventResult::Redraw
        }
        // down + cmpl: next completion
        Key {
            code: Down,
            mods: NOMOD,
        } if has_cmpls => mv_completions(state.tab_state(), true),
        // up + cmpl: prev completion
        Key {
            code: Up,
            mods: NOMOD,
        } if has_cmpls => mv_completions(state.tab_state(), false),
        // esc + cmpl: clear completions
        Key {
            code: Esc,
            mods: NOMOD,
        } if has_cmpls => {
            state.tab_state().completions.reset();
            EventResult::Redraw
        }
        // Move cursor left
        Key {
            code: Left,
            mods: NOMOD,
        } => mv_cursor(state.tab_state(), false, true),
        // Move cursor right
        Key {
            code: Right,
            mods: NOMOD,
        } => mv_cursor(state.tab_state(), false, false),
        // Move cursor left a word
        Key {
            code: Left,
            mods: KM::CONTROL,
        } => mv_cursor(state.tab_state(), true, true),
        // Move cursor right
        Key {
            code: Right,
            mods: KM::CONTROL,
        } => mv_cursor(state.tab_state(), true, false),
        // Backspace
        Key {
            code: Backspace,
            mods: NOMOD,
        }
        | Key {
            code: Backspace,
            mods: KM::SHIFT,
        } => {
            state.tab_state().input.backspace();
            EventResult::InputChanged
        }
        // Delete
        Key {
            code: Delete,
            mods: NOMOD,
        } => {
            state.tab_state().input.delete();
            EventResult::InputChanged
        }
        // up: go back in history
        Key {
            code: Up,
            mods: NOMOD,
        } => mv_history(state.tab_state(), true),
        // down: go forward in history
        Key {
            code: Down,
            mods: NOMOD,
        } => mv_history(state.tab_state(), false),
        // shift|alt + enter writes a new line
        // alt is supported because vscode does not seem to support shift + enter
        Key {
            code: Enter,
            mods: KM::SHIFT,
        }
        | Key {
            code: Enter,
            mods: KM::ALT,
        } => {
            state.tab_state().input.insert('\n');
            EventResult::InputChanged
        }
        // add character to input
        Key {
            code: Char(c),
            mods: NOMOD,
        }
        | Key {
            code: Char(c),
            mods: KM::SHIFT,
        } => {
            state.tab_state().input.insert(c);
            EventResult::InputChanged
        }
        Resize => EventResult::Redraw,
        _ => EventResult::None,
    }
}

fn mv_cursor(state: &mut TabState, mv_word: bool, mv_left: bool) -> EventResult {
    use input::Mvmt::*;
    let mvmt = if mv_word { Word } else { Ch(1) };
    if mv_left {
        state.input.move_left(mvmt);
    } else {
        state.input.move_right(mvmt);
    }
    state.completions.reset();
    EventResult::Redraw
}

fn draw<B: Backend>(term: &mut Term<B>, state: &mut TermState) -> io::Result<()> {
    term.draw(|f| draw_frame(f, state)).map(|_| ())
}

fn draw_frame<B: Backend>(frame: &mut Frame<B>, state: &mut TermState) {
    let size = frame.size();
    let draw_help = state.draw_help;

    // border
    let border = Block::default()
        .borders(Borders::LEFT | Borders::RIGHT | Borders::BOTTOM)
        .border_type(BorderType::Thick);
    let area = border.inner(size);
    frame.render_widget(border, size);

    // tabs
    let tabs = (0..state.tabs_len())
        .map(|x| format!("Tab {}", x + 1))
        .map(Spans::from)
        .collect();
    let tabs = Tabs::new(tabs)
        .style(Style::default().fg(Color::DarkGray))
        .highlight_style(
            Style::default()
                .fg(Color::White)
                .add_modifier(Modifier::BOLD | Modifier::UNDERLINED),
        )
        .select(state.tab_selected());
    let tabs_area = Rect { height: 1, ..area };
    frame.render_widget(tabs, tabs_area);

    // --
    let state = state.tab_state();
    let draw_cmpls = state.completions.has();
    let area = reduce_top_margin(area, 1);

    // title
    let title = convert_coloured_str(&state.title, std::usize::MAX)
        .lines
        .remove(0);
    let border = Block::default().title(title).borders(Borders::TOP);
    frame.render_widget(border, area);
    let area = reduce_top_margin(area, 1);

    // prompt
    let prompt_txt = Text::from(&*state.prompt);
    let prompt_area = Rect {
        width: prompt_txt.width() as u16,
        ..area
    };
    let area = Rect {
        width: area.width.saturating_sub(prompt_area.width),
        x: area.x + prompt_area.width,
        ..area
    };
    frame.render_widget(Paragraph::new(prompt_txt), prompt_area);

    // input -- calculates cursor and completion position here as well
    let input = state.input_text(area.width as usize);
    let newlines_offset = sum_newline_chars(&state.input);
    let ends_nl = |range| {
        state
            .input
            .chars(range)
            .last()
            .map(|&x| x == '\n')
            .unwrap_or(false)
    };
    let (cursorx, cursory) =
        calculate_cursor_offset(&input, state.input.ch_pos().saturating_sub(newlines_offset));
    // bit of a hack adjustment to place the cursor and cmpls window correctly.
    // is a bit wacky with multiline input
    let (cursorx, cursory) = if ends_nl(..state.input.ch_pos()) {
        (0, cursory + 1)
    } else {
        (cursorx, cursory)
    };

    let cmplx = if draw_cmpls {
        if ends_nl(..state.completions.word_pos()) {
            0
        } else {
            calculate_cursor_offset(
                &input,
                state.completions.word_pos().saturating_sub(newlines_offset),
            )
            .0
        }
    } else {
        0
    };

    let (input_area, para, area) = text_block(input, area);
    let input_area = input_area.intersection(size);
    frame.render_widget(para, input_area);
    // --cursor
    frame.set_cursor(input_area.x + cursorx, input_area.y + cursory);

    let area = Rect {
        x: prompt_area.x,
        width: prompt_area.width + area.width,
        ..area
    }; // reset x pos back to start of prompt

    // outputs
    if area.width != state.outputs.cached_width() {
        state.outputs.update_width(area.width);
    }
    let block = Block::default().title(" Outputs ").borders(Borders::TOP);
    let area2 = block.inner(area);
    frame.render_widget(block, area);
    frame.render_widget(&state.outputs, area2);

    // draw help if required
    if draw_help {
        // help draws over bottom right hand corner
        let help = help_msg();
        let (w, h) = (help.width() as u16, help.height() as u16);
        let (x, y) = (
            area.right().saturating_sub(w),
            area.bottom().saturating_sub(h),
        );
        let area = Rect::new(x, y, w, h).intersection(size);
        let para = Paragraph::new(help)
            .alignment(Alignment::Right)
            .style(Style::default().fg(Color::Black).bg(Color::Magenta));
        frame.render_widget(Clear, area);
        frame.render_widget(para, area);
    }

    // completions (last to render on top!)
    if !draw_cmpls {
        return;
    }
    let c = state.completions.items();
    let cmpls = construct_completion_block(c, state.completions.highlighted());
    let tags = construct_completion_tags(c);
    let txt_area = Rect {
        x: input_area.x + cmplx,
        y: area.y,
        width: cmpls.width() as u16,
        height: cmpls.height() as u16,
    }
    .intersection(area);
    let tag_area = Rect {
        x: txt_area.x + txt_area.width + 1,
        y: txt_area.y,
        width: tags.width() as u16,
        height: tags.height() as u16,
    };
    let tag_area = if tag_area.intersects(area) {
        Some(tag_area.intersection(area))
    } else {
        None
    };

    let bg_area = {
        let mut a = tag_area.map(|a| txt_area.union(a)).unwrap_or(txt_area);
        a.x = a.x.saturating_sub(1);
        a.width += 2;
        a.intersection(area)
    };
    let sty = completion_style();

    frame.render_widget(Clear, bg_area);
    frame.render_widget(Block::default().style(sty), bg_area);
    frame.render_widget(Paragraph::new(cmpls).style(sty), txt_area);
    if let Some(tag_area) = tag_area {
        frame.render_widget(Paragraph::new(tags).style(sty), tag_area);
    }
}

fn eval<B, E, F>(term: &mut Term<B>, mut events: E, mut f: F, state: &mut TermState)
where
    B: Backend,
    E: Iterator<Item = Event>,
    F: FnMut(Input, TabId, Cancelled) -> ConfigUpdate + Send,
{
    // prepare state
    let (input, tabid) = {
        let state = state.tab_state();
        let (input, tabid) = (state.input.buffer(..), state.id);
        state.input.clear();
        state.completions.reset();
        state.history.add(input.clone());
        (input, tabid)
    };

    // run on_enter_press on another thread
    let (donetx, donerx) = bounded(1);
    let cancelsw = Cancelled::off();

    let cu = scope(|s| {
        let compute_thread = s
            .builder()
            .name("ogma-shell-compute-thread".to_string())
            .spawn(|_| {
                let r = f(input, tabid, cancelsw.clone());
                donetx.send(()).ok();
                r
            })
            .expect("compute thread failed to start");

        // have to do the updating here while we wait for compute_thread to finish
        let msg = |s| format!("computing... ({} s) - {}", s, "Ctrl+x to abort".yellow());
        let mut sec = 0;
        state.tab_state().input.insert_str(&msg(sec));
        draw(term, state).ok(); // ignore draw errors
        let break_ev = Event::Key {
            code: KeyCode::Char('x'),
            mods: KeyModifiers::CONTROL,
        };
        loop {
            crossbeam_select! {
                recv(donerx) -> _ => break,
                default(std::time::Duration::from_secs(1)) => {
                    let cancelled = events.any(|x| x == break_ev);
                    if cancelled {
                        cancelsw.flip_on();
                    }
                    sec += 1;
                    state.tab_state().input.clear();
                    state.tab_state().input.insert_str(&msg(sec));
                    draw(term, state).ok(); // ignore draw errors
                }
            }
        }

        compute_thread.join()
    })
    .and_then(|r| r);

    // update tabstate
    state.tab_state().input.clear();
    match cu {
        Ok(cu) => state.tab_state().update(cu),
        Err(e) => match e.downcast::<String>() {
            Ok(e) => eprintln!("omga shell compute thread panicked: {}", e),
            Err(_) => eprintln!("ogma shell compute thread panicked"),
        },
    }
}

/// Returns `(paragraph area, paragraph, remaining area)`.
fn text_block(text: Text, rect: Rect) -> (Rect, Paragraph, Rect) {
    let h = cmp::max(text.height(), 1) as u16;
    let area1 = Rect { height: h, ..rect };
    let area2 = reduce_top_margin(rect, h);
    let p = Paragraph::new(text);
    (area1, p, area2)
}

/// Sums newlines characters up to cursor position of input.
/// This should be offset against character and word positions to get correct cursor positions.
fn sum_newline_chars(input: &InputBuffer) -> usize {
    input
        .chars(..input.ch_pos())
        .iter()
        .filter(|&&c| c == '\r' || c == '\n')
        .map(|x| x.len_utf8())
        .sum()
}

fn calculate_cursor_offset(text: &Text, chpos: usize) -> (u16, u16) {
    let mut x = 0;
    let mut y = 0;
    let mut w = 0;
    for line in &text.lines {
        let t = w + line.width();
        if t >= chpos {
            x = (chpos - w) as u16;
            break;
        }
        w = t;
        y += 1;
    }

    (x, y)
}

fn construct_completion_block(cmpls: &[Completion], highlighted: Option<usize>) -> Text {
    let mut lines: Vec<_> = cmpls.iter().map(|c| Spans::from(&*c.value)).collect();

    if let Some(i) = highlighted {
        if let Some(s) = lines.get_mut(i) {
            for ss in &mut s.0 {
                ss.style = ss.style.bg(Color::Cyan);
            }
        }
    }

    lines.into()
}

fn construct_completion_tags(cmpls: &[Completion]) -> Text {
    cmpls
        .iter()
        .map(|c| Spans::from(c.ty.tag()))
        .collect::<Vec<_>>()
        .into()
}

fn completion_style() -> Style {
    Style::default().bg(Color::Magenta).fg(Color::Black)
}

fn help_msg() -> Text<'static> {
    let lines = vec![
        Spans::from(Span::from("Ctrl+h: toggle help")),
        Spans::from(Span::from("Ctrl+q: close tab")),
        Spans::from(Span::from("Ctrl+t: open new tab")),
        Spans::from(Span::from("Tab: cycle tabs")),
        Spans::from(Span::from("Shift+↑|PgUp: scroll output up")),
        Spans::from(Span::from("Shift+↓|PgDown: scroll output down")),
    ];
    Text::from(lines)
}

/// Keeps bottom coordinates consistent, but moves y and height to account for `by`.
fn reduce_top_margin(rect: Rect, by: u16) -> Rect {
    let by = std::cmp::min(rect.height, by);
    Rect {
        y: rect.y + by,
        height: rect.height - by,
        ..rect
    }
}

fn mv_history(state: &mut TabState, back: bool) -> EventResult {
    if back {
        state.history.back();
    } else {
        state.history.fwd();
    }

    state.input.clear();
    state
        .input
        .insert_str(state.history.current().unwrap_or(""));
    state.completions.reset();
    EventResult::Redraw
}

fn mv_completions(state: &mut TabState, next: bool) -> EventResult {
    let start = state.completions.word_pos();

    let (len, with) = if next {
        state.completions.highlight_next()
    } else {
        state.completions.highlight_prev()
    };

    let input = &mut state.input;
    input.move_start();
    input.move_right(input::Mvmt::Ch(start));
    for _ in 0..len {
        input.delete();
    }
    input.insert_str(with);

    EventResult::Redraw
}

// ###### TEXT DECORATIONS #####################################################
fn convert_coloured_str(s: &str, width: usize) -> Text<'static> {
    use unicode_width::*;

    let mut lines = Vec::new();
    for line in cansi::line_iter(&cansi::categorise_text(s)) {
        // each new line actually needs to account for the width of the new line characters
        // it is a bit tricky to work out if it will be a \r\n or \n
        let mut w = 0;
        let mut spans = Vec::new();
        for slice in line {
            let mut i = 0;
            let mut start = 0;
            for ch in slice.text.chars() {
                let chw = ch.width().unwrap_or(0);
                w += chw;
                if w > width {
                    spans.push(cnv_span(&slice.text[start..i], slice));
                    lines.push(Spans::from(spans));
                    spans = vec![];
                    start = i;
                    w = chw;
                }
                i += ch.len_utf8();
            }
            spans.push(cnv_span(&slice.text[start..i], slice));
        }

        lines.push(Spans::from(spans));
    }

    // if text ends with a new line, line iter won't have the extra line (excludes trailing line if
    // empty)
    if s.ends_with('\n') {
        lines.push(Spans::from(vec![Span::from("")]));
    }

    lines.into()
}

fn cnv_span(s: &str, slice: cansi::CategorisedSlice) -> Span<'static> {
    let mut style = Style {
        fg: Some(cnv_colour(slice.fg_colour)),
        bg: Some(cnv_colour(slice.bg_colour)),
        ..Default::default()
    };

    style = match slice.intensity {
        cansi::Intensity::Bold => style.add_modifier(Modifier::BOLD),
        cansi::Intensity::Faint => style.add_modifier(Modifier::DIM),
        cansi::Intensity::Normal => style,
    };
    if slice.italic {
        style = style.add_modifier(Modifier::ITALIC);
    }
    if slice.underline {
        style = style.add_modifier(Modifier::UNDERLINED);
    }
    if slice.blink {
        style = style.add_modifier(Modifier::RAPID_BLINK);
    }
    if slice.reversed {
        style = style.add_modifier(Modifier::REVERSED);
    }
    if slice.hidden {
        style = style.add_modifier(Modifier::HIDDEN);
    }
    if slice.strikethrough {
        style = style.add_modifier(Modifier::CROSSED_OUT);
    }

    Span::styled(String::from(s), style)
}

fn cnv_colour(c: cansi::Color) -> Color {
    use cansi::Color::*;

    match c {
        Black => Color::Black,
        Red => Color::Red,
        Green => Color::Green,
        Yellow => Color::Yellow,
        Blue => Color::Blue,
        Magenta => Color::Magenta,
        Cyan => Color::Cyan,
        White => Color::White,
        BrightBlack => Color::DarkGray,
        BrightRed => Color::LightRed,
        BrightGreen => Color::LightGreen,
        BrightYellow => Color::LightYellow,
        BrightBlue => Color::LightBlue,
        BrightMagenta => Color::LightMagenta,
        BrightCyan => Color::LightCyan,
        BrightWhite => Color::White,
    }
}

#[cfg(test)]
mod unit_tests {
    use super::*;

    #[test]
    fn cursor_offset() {
        let f = calculate_cursor_offset;
        let text = &Text::from("Hello");
        assert_eq!(f(text, 0), (0, 0));
        assert_eq!(f(text, 1), (1, 0));
        assert_eq!(f(text, 2), (2, 0));
        assert_eq!(f(text, 3), (3, 0));
        assert_eq!(f(text, 4), (4, 0));
        assert_eq!(f(text, 5), (5, 0));
        assert_eq!(f(text, 6), (0, 1));
        let text = &Text::from("Hello\nWorld");
        assert_eq!(f(text, 0), (0, 0));
        assert_eq!(f(text, 1), (1, 0));
        assert_eq!(f(text, 4), (4, 0));
        assert_eq!(f(text, 5), (5, 0));
        assert_eq!(f(text, 6), (1, 1));
        assert_eq!(f(text, 9), (4, 1));
        assert_eq!(f(text, 10), (5, 1));

        // ending with a new line
        let text = &Text::from("\n");
        assert_eq!(f(text, 0), (0, 0));
        assert_eq!(f(text, 1), (0, 1));
        assert_eq!(f(text, 2), (0, 1));

        // ending with a new line
        let text = &Text::from("Hello\n");
        assert_eq!(f(text, 0), (0, 0));
        assert_eq!(f(text, 1), (1, 0));
        assert_eq!(f(text, 2), (2, 0));
        assert_eq!(f(text, 3), (3, 0));
        assert_eq!(f(text, 4), (4, 0));
        assert_eq!(f(text, 5), (5, 0));
        assert_eq!(f(text, 6), (0, 1));
        assert_eq!(f(text, 7), (0, 1));
    }

    #[test]
    fn reduce_rect() {
        let r = |y, h| Rect::new(0, y, 10, h);
        let x = reduce_top_margin(r(0, 5), 1);
        assert_eq!(x, r(1, 4));

        let x = reduce_top_margin(x, 2);
        assert_eq!(x, r(3, 2));

        let x = reduce_top_margin(x, 3);
        assert_eq!(x, r(5, 0));

        let x = reduce_top_margin(x, 4);
        assert_eq!(x, r(5, 0));
    }

    #[test]
    fn text_block_test() {
        let r = |y, h| Rect::new(0, y, 10, h);
        let (r1, _, r2) = text_block("".into(), r(0, 5));
        assert_eq!(r1, r(0, 1));
        assert_eq!(r2, r(1, 4));
    }

    #[test]
    fn multiline_text_decorating() {
        let text = |s| Text::styled(s, Style::default().fg(Color::White).bg(Color::Black));

        let t = "Hello, world!";
        let txt = convert_coloured_str(t, 4);
        let exp = text(
            "Hell
o, w
orld
!",
        );
        assert_eq!(txt, exp);
    }

    #[test]
    fn converting_cansi() {
        use ::libs::colored::*;

        ::libs::colored::control::set_override(true);

        let colours = format!(
            "{}{}{}{}{}{}{}{}{}",
            "red-underlined".red().on_black().underline(),
            "blue-bold".blue().on_green().bold(),
            "yellow-faint".yellow().on_white().dimmed(),
            "purple-italic".purple().on_cyan().italic(),
            "cyan-blink".cyan().on_yellow().blink(),
            "bright-black-reversed"
                .bright_black()
                .on_bright_red()
                .reversed(),
            "bright-green-hidden"
                .bright_green()
                .on_bright_yellow()
                .hidden(),
            "bright-blue-strikethrough"
                .bright_blue()
                .on_bright_purple()
                .strikethrough(),
            "cyan".bright_cyan().on_bright_white()
        );
        let text = convert_coloured_str(&colours, 300);
        let output = format!("{:?}", text);
        println!("{}", output);
        assert_eq!(
            &output,
            r#"Text { lines: [Spans([Span { content: "red-underlined", style: Style { fg: Some(Red), bg: Some(Black), add_modifier: UNDERLINED, sub_modifier: (empty) } }, Span { content: "blue-bold", style: Style { fg: Some(Blue), bg: Some(Green), add_modifier: BOLD, sub_modifier: (empty) } }, Span { content: "yellow-faint", style: Style { fg: Some(Yellow), bg: Some(White), add_modifier: DIM, sub_modifier: (empty) } }, Span { content: "purple-italic", style: Style { fg: Some(Magenta), bg: Some(Cyan), add_modifier: ITALIC, sub_modifier: (empty) } }, Span { content: "cyan-blink", style: Style { fg: Some(Cyan), bg: Some(Yellow), add_modifier: RAPID_BLINK, sub_modifier: (empty) } }, Span { content: "bright-black-reversed", style: Style { fg: Some(DarkGray), bg: Some(LightRed), add_modifier: REVERSED, sub_modifier: (empty) } }, Span { content: "bright-green-hidden", style: Style { fg: Some(LightGreen), bg: Some(LightYellow), add_modifier: HIDDEN, sub_modifier: (empty) } }, Span { content: "bright-blue-strikethrough", style: Style { fg: Some(LightBlue), bg: Some(LightMagenta), add_modifier: CROSSED_OUT, sub_modifier: (empty) } }, Span { content: "cyan", style: Style { fg: Some(LightCyan), bg: Some(White), add_modifier: (empty), sub_modifier: (empty) } }])] }"#
        );
    }

    #[test]
    fn converting_cansi_newline() {
        let colours = "\n";
        let text = convert_coloured_str(colours, 300);
        let output = format!("{:?}", text);
        println!("{}", output);
        assert_eq!(
            &output,
            "Text { lines: [\
Spans([Span { content: \"\", style: Style { fg: Some(White), bg: Some(Black), add_modifier: (empty), sub_modifier: (empty) } }]), \
Spans([Span { content: \"\", style: Style { fg: None, bg: None, add_modifier: (empty), sub_modifier: (empty) } }])\
] }"
        );
    }
}
