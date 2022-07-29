use tui::style::*;

pub trait Theme {
    fn theme(self, theme: u8) -> Self;
}

impl Theme for Style {
    fn theme(self, theme: u8) -> Self {
        let t = theme % 2;
        debug_assert!(t < 2, "remember to have a theme for each mod");
        match t {
            0 => self, // default theme,
            1 => apply::<Light>(self),
            x => unreachable!("{x} theme not handled"),
        }
    }
}

fn apply<Th: Alter>(mut style: Style) -> Style {
    fn apply_mod(style: Style, m: Modifier, add: bool, rm: bool) -> Style {
        match style.add_modifier.contains(m) {
            true if rm => style.remove_modifier(m),
            false if add => style.add_modifier(m),
            _ => style,
        }
    }

    style.fg = style.fg.map(Th::colour);
    style.bg = style.bg.map(Th::colour);

    style = apply_mod(style, Modifier::BOLD, Th::add_bold(), Th::rm_bold());
    style = apply_mod(
        style,
        Modifier::UNDERLINED,
        Th::add_underline(),
        Th::rm_underline(),
    );

    style
}

trait Alter {
    fn colour(c: Color) -> Color {
        c
    }

    fn add_bold() -> bool {
        false
    }

    fn rm_bold() -> bool {
        false
    }

    fn add_underline() -> bool {
        false
    }

    fn rm_underline() -> bool {
        false
    }
}

struct Light;

impl Alter for Light {
    fn colour(c: Color) -> Color {
        use Color::*;

        match c {
            White => Black,
            Magenta => LightMagenta,
            LightCyan => Cyan,
            LightRed => Red,
            Yellow => Rgb(210, 105, 30),
            // help and completions text,
            Rgb(192, 192, 192) => Rgb(55,55,55),
            x => x,
        }
    }
}
