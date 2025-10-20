use aho_corasick::{AhoCorasick, MatchKind};
use regex::Regex;
use std::io::{Read, Write};
use std::{iter, sync::LazyLock};

fn main() {
    let mut stdin = std::io::stdin();
    let mut stdout = std::io::stdout();
    let mut buf = String::new();
    let (glyphs, words) = expand(&GLYPHS_WORDS);

    let _ = stdin.read_to_string(&mut buf);
    let _ = write!(stdout, "{}", replace(&buf, &words, &glyphs));
}

fn expand(inp: &[(&str, Vec<Vec<&str>>)]) -> (Vec<String>, Vec<String>) {
    fn prefixes<'a>(repl: &'a [&str]) -> Box<dyn Iterator<Item = String> + 'a> {
        match repl {
            [] => Box::new(vec![].into_iter()),
            [v] => Box::new(vec![v.to_string()].into_iter()),
            [p, s] => Box::new(
                s.char_indices()
                    .map(|(pos, _)| &s[..pos])
                    .chain(iter::once(*s))
                    .map(move |s| p.to_string() + s),
            ),
            _ => unreachable!(),
        }
    }

    inp.iter()
        .flat_map(|(glyph, words)| {
            words
                .iter()
                .flat_map(|ws| prefixes(ws))
                .map(|s| (glyph.to_string(), s))
        })
        .unzip()
}

fn replace(inp: &str, from: &[String], to: &[String]) -> String {
    let mut res = String::new();
    let mut end = 0;
    let repl = AhoCorasick::builder()
        .match_kind(MatchKind::LeftmostLongest)
        .build(from)
        .unwrap();

    fn rep_with(repl: &AhoCorasick, slice: &str, to: &[String], res: &mut String) {
        repl.replace_all_with(slice, res, |mat, matstr, dst| {
            // Don't replace string if the char before the match is an
            // underscore; this is to prevent _add being changed into _+.
            // Some examples of this are in the BQN stdlib.
            let i = mat.start().max(1) - 1;
            if Some("_") == slice.get(i..i + 1) {
                dst.push_str(matstr.as_ref());
            } else {
                dst.push_str(to[mat.pattern()].as_ref());
            }
            true
        })
    }

    Regex::new(r#"(?m:((?:^|[^'])#[^\n]*(?:\n|$))|((?:^|[^'])"(?:[^"]|"")*"))"#) // excludes
        .unwrap()
        .captures_iter(inp)
        .map(|c| c.get(0).unwrap())
        .for_each(|e| {
            rep_with(&repl, &inp[end..e.start()], to, &mut res); // Region before match -> replace.
            res.push_str(e.as_str()); // Add last excluded region unchanged.
            end = e.end();
        });
    rep_with(&repl, &inp[end..inp.len()], to, &mut res); // Add final region.

    res
}

#[allow(clippy::type_complexity)]
static GLYPHS_WORDS: LazyLock<Vec<(&str, Vec<Vec<&str>>)>> = LazyLock::new(|| {
    [
        ("+", vec![vec!["conj", "ugate"], vec!["add"]]),
        ("×", vec![vec!["sign"], vec!["mul", "tiply"]]),
        ("÷", vec![vec!["recip", "rocal"], vec!["div", "ide"]]),
        ("⇐", vec![vec!["expo", "rt"]]),
        ("⋆", vec![vec!["exp", "onential"], vec!["pow", "er"]]),
        ("√", vec![vec!["sqrt"], vec!["root"]]),
        ("¯", vec![vec!["minus"]]),
        ("⌊", vec![vec!["floor"], vec!["min", "imum"]]),
        ("⌈", vec![vec!["ceil", "ing"], vec!["max", "imum"]]),
        ("|", vec![vec!["abs"], vec!["mod", "ulus"]]),
        ("·", vec![vec!["noth", "ing"]]),
        ("≠", vec![vec!["len", "gth"], vec!["noteq", "uals"]]),
        ("≢", vec![vec!["shape"], vec!["notmatch"]]),
        ("¬", vec![vec!["not"], vec!["span"]]),
        ("∧", vec![vec!["sortup"], vec!["land"]]),
        ("∨", vec![vec!["sortdown"], vec!["lor"]]),
        ("<", vec![vec!["encl", "ose"], vec!["less"]]),
        (">", vec![vec!["merge"], vec!["greater"]]),
        ("=", vec![vec!["rank"], vec!["eq", "uals"]]),
        ("≤", vec![vec!["leq"]]),
        ("≥", vec![vec!["geq"]]),
        ("≡", vec![vec!["depth"], vec!["match"]]),
        ("⊣", vec![vec!["left"]]),
        ("⊢", vec![vec!["ident", "ity"], vec!["right"]]),
        ("⥊", vec![vec!["desh", "ape"], vec!["resh", "ape"]]),
        ("∾", vec![vec!["join"], vec!["jointo"]]),
        ("≍", vec![vec!["solo"], vec!["coup", "le"]]),
        ("↑", vec![vec!["prefi", "xes"], vec!["take"]]),
        ("↕", vec![vec!["range"], vec!["wind", "ows"]]),
        ("↓", vec![vec!["suffi", "xes"], vec!["drop"]]),
        ("»", vec![vec!["nudge"], vec!["shifta", "fter"]]),
        ("«", vec![vec!["nudgeb", "ack"], vec!["shiftb", "efore"]]),
        ("⌽", vec![vec!["rev", "erse"], vec!["rot", "ate"]]),
        ("⍉", vec![vec!["trans", "pose"], vec!["reorderaxes"]]),
        ("/", vec![vec!["indi", "ces"], vec!["repli", "cate"]]),
        ("⍋", vec![vec!["gradeup"], vec!["binsup"]]),
        ("⍒", vec![vec!["graded", "own"], vec!["binsd", "own"]]),
        ("⊏", vec![vec!["firstc", "ell"], vec!["sel", "ect"]]),
        ("⊑", vec![vec!["first"], vec!["pick"]]),
        ("⊐", vec![vec!["classi", "fy"], vec!["indexof"]]),
        (
            "⊒",
            vec![vec!["occu", "rrencecount"], vec!["prog", "ressiveindexof"]],
        ),
        ("∊", vec![vec!["markf", "irsts"], vec!["mem", "berof"]]),
        ("⍷", vec![vec!["dedup", "licate"], vec!["find"]]),
        ("⊔", vec![vec!["groupi", "ndices"], vec!["group"]]),
        ("!", vec![vec!["assert"]]),
        ("-", vec![vec!["neg", "ate"], vec!["sub", "tract"]]),
        ("˙", vec![vec!["const", "ant"]]),
        ("˜", vec![vec!["sel", "f"], vec!["swa", "p"]]),
        ("˘", vec![vec!["cells"]]),
        ("¨", vec![vec!["each"]]),
        ("⌜", vec![vec!["table"]]),
        ("⁼", vec![vec!["undo"]]),
        ("´", vec![vec!["fold"]]),
        ("˝", vec![vec!["insert"]]),
        ("`", vec![vec!["scan"]]),
        ("∘", vec![vec!["atop"]]),
        ("○", vec![vec!["over"]]),
        ("⊸", vec![vec!["bindl", "eft"], vec!["befo", "re"]]),
        ("⟜", vec![vec!["bindr", "ight"], vec!["aft", "er"]]),
        ("⌾", vec![vec!["under"]]),
        ("⊘", vec![vec!["vale", "nces"]]),
        ("◶", vec![vec!["choo", "se"]]),
        ("⎉", vec![vec!["Rank"]]),
        ("⚇", vec![vec!["Depth"]]),
        ("⍟", vec![vec!["repe", "at"]]),
        ("⎊", vec![vec!["catch"]]),
        ("←", vec![vec!["defi", "ne"]]),
        ("↩", vec![vec!["modi", "fy"], vec!["chan", "ge"]]),
        ("⟨", vec![vec!["langle"], vec!["beginl", "ist"]]),
        ("⟩", vec![vec!["rangle"], vec!["endl", "ist"]]),
        ("π", vec![vec!["npi"]]),
        ("∞", vec![vec!["infty"], vec!["infi", "nity"]]),
        ("‿", vec![vec!["stra", "nd"]]),
        ("𝕩", vec![vec!["xx"]]),
        ("𝕏", vec![vec!["XX"]]),
        ("𝕨", vec![vec!["ww"]]),
        ("𝕎", vec![vec!["WW"]]),
        ("𝕗", vec![vec!["fff"]]),
        ("𝔽", vec![vec!["FFF"]]),
        ("𝕘", vec![vec!["ggg"]]),
        ("𝔾", vec![vec!["GGG"]]),
        ("𝕣", vec![vec!["rrr"]]),
        ("𝕤", vec![vec!["sss"]]),
        ("𝕊", vec![vec!["SSS"]]),
    ]
    .into()
});

#[cfg(test)]
mod tests {
    #[test]
    fn simple() {
        use super::*;
        let s = r#"
# Comment mul
v ← mul # mul is ×
s ← "a string mul and ""so on ×"""
"#;
        let (glyphs, words) = expand(&GLYPHS_WORDS);
        let res = replace(s, &words, &glyphs);
        assert!(res.contains("v ← ×"));
        assert!(res.contains(r#"s ← "a string mul and ""so on ×""""#));
    }

    #[test]
    fn underscore() {
        use super::*;
        let (glyphs, words) = expand(&GLYPHS_WORDS);
        let res = replace("P ← 32‿1•bit._add⌾⌽", &words, &glyphs);
        assert!(res == "P ← 32‿1•bit._add⌾⌽");
    }

    #[test]
    fn totp_idempotent() {
        use super::*;
        let (glyphs, words) = expand(&GLYPHS_WORDS);
        let s = std::fs::read_to_string("./test_data/totp.bqn").unwrap();
        assert!(s == replace(&s, &words, &glyphs));
    }

    #[test]
    fn char_quote() {
        use super::*;
        let (glyphs, words) = expand(&GLYPHS_WORDS);
        let s = r#"sss'"'sss'"'sss"#;
        assert!(r#"𝕤'"'𝕤'"'𝕤"# == replace(s, &words, &glyphs));
    }

    #[test]
    fn char_hash() {
        use super::*;
        let (glyphs, words) = expand(&GLYPHS_WORDS);
        let s = r#"sss'#'sss"#;
        assert!(r#"𝕤'#'𝕤"# == replace(s, &words, &glyphs));
    }
}
