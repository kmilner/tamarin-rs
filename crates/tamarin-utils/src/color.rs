// Currently GPL 3.0 until granted permission by the following authors:
//   meiersi
// Ported from upstream tamarin-prover sources:
//   lib/utils/src/Data/Color.hs

//! Port of `Data.Color` from `lib/utils/src/Data/Color.hs`.
//!
//! RGB and HSV color types with conversions and palette generation.
//! Floats are used throughout (`f64`); the original is generic over
//! `Fractional`/`RealFrac`.

#[derive(Debug, Clone, Copy, PartialEq, PartialOrd)]
pub struct Rgb {
    pub r: f64,
    pub g: f64,
    pub b: f64,
}

#[derive(Debug, Clone, Copy, PartialEq, PartialOrd)]
pub struct Hsv {
    pub h: f64,
    pub s: f64,
    pub v: f64,
}

impl Rgb {
    pub const fn new(r: f64, g: f64, b: f64) -> Self { Rgb { r, g, b } }
    pub fn map<F: Fn(f64) -> f64>(self, f: F) -> Self {
        Rgb { r: f(self.r), g: f(self.g), b: f(self.b) }
    }
}

impl Hsv {
    pub const fn new(h: f64, s: f64, v: f64) -> Self { Hsv { h, s, v } }
    pub fn map<F: Fn(f64) -> f64>(self, f: F) -> Self {
        Hsv { h: f(self.h), s: f(self.s), v: f(self.v) }
    }
}

pub const RED:   Rgb = Rgb::new(1.0, 0.0, 0.0);
pub const GREEN: Rgb = Rgb::new(0.0, 1.0, 0.0);
pub const BLUE:  Rgb = Rgb::new(0.0, 0.0, 1.0);

// -- Colourspace conversions --------------------------------------------------

/// RGB → HSV. Pre: `0 <= r,g,b <= 1`.
pub fn rgb_to_hsv(c: Rgb) -> Hsv {
    let Rgb { r, g, b } = c;
    let ub = r.max(g.max(b));
    let lb = r.min(g.min(b));
    let h_raw = if ub == lb {
        0.0
    } else if ub == r {
        60.0 * ((g - b) / (ub - lb))
    } else if ub == g {
        60.0 * (2.0 + (b - r) / (ub - lb))
    } else {
        60.0 * (4.0 + (r - g) / (ub - lb))
    };
    let h = if h_raw < 0.0 { h_raw + 360.0 } else { h_raw };
    let s = if ub == 0.0 { 0.0 } else { (ub - lb) / ub };
    Hsv { h, s, v: ub }
}

/// HSV → RGB. Pre: `0 <= h <= 360`, `0 <= s,v <= 1`.
pub fn hsv_to_rgb(c: Hsv) -> Rgb {
    let Hsv { h, s, v } = c;
    let h_idx = (h / 60.0).floor() as i32;
    let f = h / 60.0 - h_idx as f64;
    let p = v * (1.0 - s);
    let q = v * (1.0 - s * f);
    let t = v * (1.0 - s * (1.0 - f));
    match h_idx {
        0 => Rgb::new(v, t, p),
        1 => Rgb::new(q, v, p),
        2 => Rgb::new(p, v, t),
        3 => Rgb::new(p, q, v),
        4 => Rgb::new(t, p, v),
        5 => Rgb::new(v, p, q),
        _ => panic!("hsv_to_rgb: hue outside [0,360]"),
    }
}

/// Drop saturation, keeping hue and value (used to render greyscale variants).
pub fn hsv_to_gray(c: Hsv) -> Hsv {
    Hsv { h: c.h, s: 0.0, v: c.v }
}

/// `rgbToGray`: max channel intensity.
pub fn rgb_to_gray(c: Rgb) -> f64 { c.r.max(c.g.max(c.b)) }

// -- Hex output ---------------------------------------------------------------

pub fn rgb_to_hex(c: Rgb) -> String {
    fn channel(f: f64) -> String {
        let i = (256.0 * f).floor() as i32;
        let i = i.clamp(0, 255);
        format!("{:02x}", i)
    }
    format!("#{}{}{}", channel(c.r), channel(c.g), channel(c.b))
}

pub fn hex_to_rgb(s: &str) -> Option<Rgb> {
    // Haskell `hexToRGB [r1,r2,g1,g2,b1,b2]` matches exactly six CHARACTERS;
    // anything else falls through to `Nothing`. Collect chars (rather than
    // byte-slicing) so multibyte input yields `None` instead of panicking on a
    // char-boundary split.
    let cs: Vec<char> = s.chars().collect();
    if cs.len() != 6 { return None; }
    let r = u8::from_str_radix(&cs[0..2].iter().collect::<String>(), 16).ok()?;
    let g = u8::from_str_radix(&cs[2..4].iter().collect::<String>(), 16).ok()?;
    let b = u8::from_str_radix(&cs[4..6].iter().collect::<String>(), 16).ok()?;
    Some(Rgb {
        r: r as f64 / 255.0,
        g: g as f64 / 255.0,
        b: b as f64 / 255.0,
    })
}

pub fn hsv_to_hex(c: Hsv) -> String { rgb_to_hex(hsv_to_rgb(c)) }

// -- Palette generation -------------------------------------------------------
//
// Faithful `Color.hs` port. `light_color_groups` — with its helpers
// `light_color_group_style`, `gen_color_groups` and `ColorParams` — is live in
// `tamarin-server`'s dot renderer, which colours rule groups through this
// palette; `hex_to_rgb` is live in `tamarin-theory::elaborate`; and
// `rgb_to_hsv`/`hsv_to_rgb`/`rgb_to_hex`/`Rgb`/`Hsv` above are live in
// `tamarin-sapic`/`tamarin-server`. The remaining `Color.hs` helpers
// (`color_groups`/`color_group_style`, `hsv_to_hex`, `hsv_to_gray`,
// `rgb_to_gray`) have no caller and are retained for completeness of the port.

#[derive(Debug, Clone, Copy)]
pub struct ColorParams {
    pub scale: f64,
    pub zero_hue: f64,
    pub v_bottom: f64,
    pub v_range: f64,
    pub s_bottom: f64,
    pub s_range: f64,
}

pub fn color_group_style(zero_hue: f64) -> ColorParams {
    ColorParams { scale: 0.6, zero_hue, v_bottom: 0.75, v_range: 0.2, s_bottom: 0.4, s_range: 0.0 }
}

pub fn light_color_group_style(zero_hue: f64) -> ColorParams {
    ColorParams { scale: 0.6, zero_hue, v_bottom: 0.8, v_range: 0.15, s_bottom: 0.3, s_range: 0.0 }
}

/// `genColorGroups`: assign every element a unique HSV colour from a layout
/// of group sizes.
pub fn gen_color_groups(p: ColorParams, groups: &[usize]) -> Vec<((usize, usize), Hsv)> {
    let n_groups = groups.len();
    if n_groups == 0 { return vec![]; }

    let to_group_hue = |g: usize, h: f64| -> f64 {
        (g as f64 + 0.5 * (1.0 - p.scale) + h * p.scale) / (n_groups as f64)
    };
    let to_shifted_group_hue = |g: usize, h: f64| -> f64 {
        let raw = to_group_hue(g, h) + 1.0 + (p.zero_hue / 360.0) - to_group_hue(0, 0.5);
        // proper_fraction: take the fractional part toward zero.
        raw - raw.trunc()
    };

    let mut out = Vec::new();
    for (group_idx, &group_size) in groups.iter().enumerate() {
        for elem_idx in 0..group_size {
            // The loop excludes `group_size == 0`, so the division is always
            // safe (mirrors Haskell's lazy `[0..groupSize-1]` comprehension).
            let frac = elem_idx as f64 / group_size as f64;
            let h = to_shifted_group_hue(group_idx, frac);
            let v = p.v_bottom + p.v_range * to_group_hue(group_idx, frac);
            let s = p.s_bottom + p.s_range * to_group_hue(group_idx, frac);
            out.push(((group_idx, elem_idx), Hsv { h: 360.0 * h, s, v }));
        }
    }
    out
}

pub fn color_groups(zero_hue: f64, groups: &[usize]) -> Vec<((usize, usize), Hsv)> {
    gen_color_groups(color_group_style(zero_hue), groups)
}

pub fn light_color_groups(zero_hue: f64, groups: &[usize]) -> Vec<((usize, usize), Hsv)> {
    gen_color_groups(light_color_group_style(zero_hue), groups)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn approx_eq(a: f64, b: f64) -> bool { (a - b).abs() < 1e-9 }

    #[test]
    fn rgb_hsv_roundtrip_primaries() {
        for &(rgb, expected_h) in
            &[(RED, 0.0), (GREEN, 120.0), (BLUE, 240.0)]
        {
            let hsv = rgb_to_hsv(rgb);
            assert!(approx_eq(hsv.h, expected_h));
            assert!(approx_eq(hsv.s, 1.0));
            assert!(approx_eq(hsv.v, 1.0));
            let back = hsv_to_rgb(hsv);
            assert!(approx_eq(back.r, rgb.r));
            assert!(approx_eq(back.g, rgb.g));
            assert!(approx_eq(back.b, rgb.b));
        }
    }

    #[test]
    fn hex_round_trip() {
        // floor(256 * 0.5) = 128 = 0x80; matches Haskell's `floor (256 * f)`.
        let rgb = Rgb::new(1.0, 0.5, 0.0);
        let h = rgb_to_hex(rgb);
        assert_eq!(h, "#ff8000");
        let back = hex_to_rgb(&h[1..]).unwrap();
        assert!((back.r - 1.0).abs() < 1e-9);
        assert!((back.g - 128.0 / 255.0).abs() < 1e-9);
        assert!((back.b - 0.0).abs() < 1e-9);
    }

    #[test]
    fn rgb_hex_clamps() {
        assert_eq!(rgb_to_hex(Rgb::new(2.0, -1.0, 0.5)), "#ff0080");
    }

    #[test]
    fn hex_to_rgb_rejects_bad_input() {
        assert!(hex_to_rgb("zzzzzz").is_none());
        assert!(hex_to_rgb("ff00").is_none());
    }

    #[test]
    fn rgb_to_gray_basic() {
        assert!(approx_eq(rgb_to_gray(Rgb::new(0.2, 0.7, 0.4)), 0.7));
    }

    #[test]
    fn color_groups_correct_size_and_distinct() {
        let g = color_groups(0.0, &[3, 2, 4]);
        assert_eq!(g.len(), 9);
        let mut idxs: Vec<(usize, usize)> = g.iter().map(|(i, _)| *i).collect();
        idxs.sort();
        idxs.dedup();
        assert_eq!(idxs.len(), 9);
        // Hues should be in [0, 360).
        for ((_, _), hsv) in &g {
            assert!(hsv.h >= 0.0 && hsv.h < 360.0);
        }
    }
}
