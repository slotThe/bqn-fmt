use std::{env, io::{Read, Write}, iter, process::exit, sync::LazyLock};

use aho_corasick::{AhoCorasick, Match, MatchKind};
use regex::Regex;

#[derive(Debug)]
enum Replace {
    Unknown,
    Known,
}

fn main() {
    let mut stdin = std::io::stdin();
    let mut stdout = std::io::stdout();
    let mut buf = String::new();
    let (glyphs, words) = expand(&GLYPHS_WORDS);

    let mut r = Replace::Known;
    let args: Vec<String> = env::args().skip(1).collect();
    match args.iter().map(|s| s as &str).collect::<Vec<_>>()[..] {
        ["--help", ..] => {
            println!(
                r#"bqn-fmt: Word-based input of BQN symbols.
USAGE: bqn-fmt [-u|--unknown-words]
OPTIONS:
  -u,--unknown-words	Expand variable even if it contains unknown
                        words: addunk → +unk"#
            );
            exit(0);
        },
        ["-u" | "--unknown-words", ..] => {
            r = Replace::Unknown;
        },
        _ => {},
    }

    let _ = stdin.read_to_string(&mut buf);
    let _ = write!(stdout, "{}", replace(&buf, &words, &glyphs, &r));
}

/// Expand the regular expressions so that all prefixes are matched. E.g., a
/// single ("⌽", [["rev","erse"]]) would yield
/// (["⌽","⌽","⌽","⌽","⌽"], ["rev","reve","rever","revers","reverse"])
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

/// Replace words with symbols.
fn replace(inp: &str, from: &[String], to: &[String], r: &Replace) -> String {
    let mut res = String::with_capacity(inp.len()); // res is shorter
    let mut end = 0;
    let re = AhoCorasick::builder()
        .match_kind(MatchKind::LeftmostLongest)
        .build(from)
        .unwrap();

    Regex::new(r#"(?m:'.?'|#[^\n]*(\n|$)|"([^"]|"")*")"#) // excludes
        .unwrap()
        .captures_iter(inp)
        .map(|c| c.get(0).unwrap())
        .for_each(|e| {
            replace_slice(&re, &inp[end..e.start()], to, &mut res, r); // Region before match -> replace.
            res.push_str(e.as_str()); // Add last excluded region unchanged.
            end = e.end();
        });
    replace_slice(&re, &inp[end..inp.len()], to, &mut res, r); // Add final region.

    res
}

/// Replace a single slice.
fn replace_slice(
    repl: &AhoCorasick,
    slice: &str,
    to: &[String],
    res: &mut String,
    r: &Replace,
) {
    let mut dst = String::with_capacity(slice.len());
    let matches: Vec<Match> = repl.find_iter(slice).collect();
    let mut lm = 0; // last match

    for (i, m) in matches.iter().enumerate() {
        dst.push_str(&slice[lm..m.start()]);
        lm = m.end();
        if dst.ends_with('_') || r.dont_replace()(&dst, slice, &matches, m, i) {
            dst.push_str(&slice[m.start()..m.end()]);
        } else {
            dst.push_str(to[m.pattern()].as_ref());
        }
    }
    dst.push_str(&slice[lm..]);

    res.push_str(&dst);
}

impl Replace {
    fn dont_replace(&self) -> fn(&str, &str, &[Match], &Match, usize) -> bool {
        match self {
            Replace::Unknown => |_, _, _, _, _| false,
            Replace::Known => |dst, slice, ms, m, i| {
                dst.ends_with(|c: char| c.is_ascii_alphabetic()) || {
                    // Unknown expansion in the first word of the slice?
                    let max: usize = m.end()
                        + slice[m.end()..]
                            .find(|c: char| !(c.is_ascii_alphabetic() || c == '_'))
                            .unwrap_or(slice[m.end()..].len());
                    let ends: Vec<&Match> =
                        ms[i..].iter().take_while(move |n| n.end() <= max).collect();
                    // First condition shields against adddivunknown and
                    // second one is for addunknowndiv.
                    ends[ends.len() - 1].end() != max
                        || ends.windows(2).any(|xy| xy[0].end() != xy[1].start())
                }
            },
        }
    }
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
        ("𝕗", vec![vec!["ff"]]),
        ("𝔽", vec![vec!["FF"]]),
        ("𝕘", vec![vec!["gg"]]),
        ("𝔾", vec![vec!["GG"]]),
        ("𝕣", vec![vec!["rr"]]),
        ("𝕤", vec![vec!["ss"]]),
        ("𝕊", vec![vec!["SS"]]),
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
        let s = r#"ss'"'ss'"'ss"#;
        assert!(r#"𝕤'"'𝕤'"'𝕤"# == replace(s, &words, &glyphs));
    }

    #[test]
    fn char_hash() {
        use super::*;
        let (glyphs, words) = expand(&GLYPHS_WORDS);
        let s = r#"ss'#'ss"#;
        assert!(r#"𝕤'#'𝕤"# == replace(s, &words, &glyphs));
    }

    #[test]
    fn char_string_concat() {
        use super::*;
        let (glyphs, words) = expand(&GLYPHS_WORDS);
        assert!("\"not\"'#'¬" == replace("\"not\"'#'not", &words, &glyphs));
        let s1 = r#"-⟜'#'"not""#;
        assert!(s1 == replace(s1, &words, &glyphs));
        let s2 = r#"negateafter'#'"mul""not""fold"add"#;
        assert!(r#"-⟜'#'"mul""not""fold"+"# == replace(s2, &words, &glyphs));
    }

    #[test]
    fn dont_expand_unknown_vars() {
        use super::*;
        let (glyphs, words) = expand(&GLYPHS_WORDS);
        assert!("xxWord +´÷≠" == replace("xxWord addfolddivlen", &words, &glyphs));
        assert!("wordxx" == replace("wordxx", &words, &glyphs));
        assert!("addfoldWord" == replace("addfoldWord", &words, &glyphs));
        assert!("|10" == replace("mod10", &words, &glyphs));
        assert!("1⌽⌽𝕩" == replace("1⌽reve𝕩", &words, &glyphs));
        assert!("+´" == replace("addfold", &words, &glyphs));
        assert!("addunknownadd ×´" == replace("addunknownadd mulfold", &words, &glyphs));
    }

    #[test]
    fn strings() {
        use super::*;
        let (glyphs, words) = expand(&GLYPHS_WORDS);
        let s = r#"classTag ← ""‿"" ∾ > {⟨"<span class='"∾𝕩∾"'>","</span>"⟩}¨ 1↓classes"#;
        assert!(s == replace(s, &words, &glyphs))
    }
}
