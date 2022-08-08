use super::*;
use std::{cmp::*, collections::VecDeque};
use tui::buffer::Buffer;

#[derive(Clone)]
pub struct Outputs {
    items: VecDeque<Output>,
    limit: usize,
    cached_width: u16,
    scroll: u16,
}

#[derive(Clone)]
struct Output {
    cached: Text<'static>,
    value: String,
}

impl Outputs {
    pub fn new(width: u16, limit: usize) -> Self {
        Outputs {
            items: VecDeque::new(),
            limit,
            cached_width: width,
            scroll: 0,
        }
    }

    pub fn cached_width(&self) -> u16 {
        self.cached_width
    }

    /// Items are in oldest to newest order.
    pub fn iter(&self) -> impl DoubleEndedIterator<Item = &Text> {
        self.items.iter().map(|x| &x.cached)
    }

    pub fn add(&mut self, value: String, theme: u8) {
        let w = self.cached_width.saturating_sub(1) as usize; // one column for the scroll bar
        let cached = super::convert_coloured_str(&value, w, theme);
        self.items.push_back(Output { cached, value });
        self.scroll = 0;

        if self.items.len() > self.limit {
            self.items.pop_front();
        }
    }

    pub fn update_width(&mut self, width: u16, theme: u8) {
        self.scroll = 0;
        self.cached_width = width;
        let w = width.saturating_sub(1) as usize; // one column for the scroll bar
        for item in &mut self.items {
            item.cached = super::convert_coloured_str(&item.value, w, theme);
        }
    }

    pub fn height(&self) -> usize {
        self.iter().map(|x| x.height()).sum()
    }

    pub fn as_paragraph(&self) -> Paragraph {
        let mut txt = Text::default();
        for output in self.iter().rev() {
            txt.extend(output.clone());
        }
        Paragraph::new(txt).scroll((self.scroll, 0))
    }

    pub fn scroll(&mut self, lines: i32) {
        use std::convert::*;
        match lines.cmp(&0) {
            Ordering::Equal => (),
            Ordering::Greater => {
                // increase scroll (scroll down)
                let lines: u16 = lines.try_into().unwrap();
                let h = self.height().saturating_sub(1) as u16;
                self.scroll = min(self.scroll.saturating_add(lines), h);
            }
            Ordering::Less => {
                // decrease scroll (scroll up)
                let lines: u16 = (-lines).try_into().unwrap();
                self.scroll = self.scroll.saturating_sub(lines);
            }
        }
    }
}

impl Widget for &Outputs {
    fn render(self, area: Rect, buf: &mut Buffer) {
        let parea = Rect {
            width: area.width.saturating_sub(1),
            ..area
        };
        let scroll_area = Rect {
            width: 1,
            x: area.x + parea.width,
            ..area
        };
        let scroll_loc = scroll_location(scroll_area, self.height(), self.scroll);

        Clear.render(scroll_area, buf);
        self.as_paragraph().render(parea, buf);
        Block::default()
            .style(Style::default().bg(Color::DarkGray))
            .render(scroll_area, buf);
        Block::default()
            .style(Style::default().bg(Color::Gray))
            .render(scroll_loc, buf);
    }
}

/// Returns the location of the scroll.
fn scroll_location(scroll_area: Rect, outputs_height: usize, scroll: u16) -> Rect {
    if outputs_height <= 1 {
        return scroll_area;
    }

    let out_height = outputs_height as f64;
    let scroll = scroll as f64;
    let scroll_area_height = scroll_area.height as f64;

    let height = if out_height <= scroll_area_height {
        scroll_area.height
    } else {
        ((scroll_area_height * scroll_area_height) / (out_height)).trunc() as u16
    };

    let height = min(scroll_area.height, max(height, 1));

    let bar_lim = scroll_area.height.saturating_sub(height);
    let y = (scroll / (out_height - 1.0)) * (bar_lim as f64);
    let y = min(y.trunc() as u16, bar_lim);

    Rect {
        y: scroll_area.y + y,
        height,
        ..scroll_area
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn scroll_location_test() {
        let s = scroll_location(Rect::new(0, 0, 1, 100), 10, 20);
        assert_eq!(s, Rect::new(0, 0, 1, 100));

        let s = scroll_location(Rect::new(0, 0, 1, 100), 90, 20);
        assert_eq!(s, Rect::new(0, 0, 1, 100));

        let s = scroll_location(Rect::new(0, 0, 1, 100), 120, 20);
        assert_eq!(s, Rect::new(0, 2, 1, 83));

        let s = scroll_location(Rect::new(0, 0, 1, 100), 150, 20);
        assert_eq!(s, Rect::new(0, 4, 1, 66));

        let s = scroll_location(Rect::new(0, 0, 1, 100), 200, 20);
        assert_eq!(s, Rect::new(0, 5, 1, 50));

        let s = scroll_location(Rect::new(0, 0, 1, 100), 200, 50);
        assert_eq!(s, Rect::new(0, 12, 1, 50));

        let s = scroll_location(Rect::new(0, 0, 1, 100), 200, 100);
        assert_eq!(s, Rect::new(0, 25, 1, 50));

        let s = scroll_location(Rect::new(0, 0, 1, 100), 200, 150);
        assert_eq!(s, Rect::new(0, 37, 1, 50));

        let s = scroll_location(Rect::new(0, 0, 1, 100), 200, 200);
        assert_eq!(s, Rect::new(0, 50, 1, 50));

        let s = scroll_location(Rect::new(0, 0, 1, 100), 200, 250);
        assert_eq!(s, Rect::new(0, 50, 1, 50));

        let s = scroll_location(Rect::new(0, 0, 1, 100), 200, 0);
        assert_eq!(s, Rect::new(0, 0, 1, 50));
    }
}
