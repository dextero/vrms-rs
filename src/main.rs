#[macro_use]
#[cfg(test)]
extern crate matches;
extern crate regex;
#[macro_use]
extern crate error_chain;

use std::cmp::min;
use std::fs::File;
use std::io::BufReader;
use std::io::BufRead;
use std::collections::HashSet;
use std::process::Command;
use std::process;

use regex::Regex;

error_chain! {
    foreign_links {
        Io(::std::io::Error);
        String(::std::string::FromUtf8Error);
        Regex(::regex::Error);
    }
}

fn read_licenses_from_file(file: &str) -> Result<HashSet<String>> {
    let file = File::open(file)?;
    let buf_reader = BufReader::new(file);
    let mut lines = HashSet::new();

    for line_res in buf_reader.lines() {
        lines.insert(line_res?.to_owned());
    }

    Ok(lines)
}

struct Package {
    name: String,
    license: License
}

impl Package {
    fn new(name: &str, license: License) -> Package {
        Package {
            name: name.to_owned(),
            license: license
        }
    }
}

trait PackageReader {
    fn read_packages(&self) -> Result<Vec<Package>>;
}

impl PackageReader {
    fn default() -> Box<PackageReader> {
        Box::new(RpmPackageReader::new())
    }
}

struct RpmPackageReader {}

impl RpmPackageReader {
    fn new() -> RpmPackageReader { RpmPackageReader {} }
}

impl PackageReader for RpmPackageReader {
    fn read_packages(&self) -> Result<Vec<Package>> {
        let child = Command::new("/tmp/rpm")
            .output()?;
        let mut packages = Vec::new();
        let packages_str = String::from_utf8(child.stdout)?;

        for line in packages_str.lines() {
            let words: Vec<&str> = line.split('\t').collect();
            if words.len() != 2 {
                return Err(Error::from(format!("unexpected line format: {}", line)));
            }
            let license = License::parse(words[1])
                .chain_err(|| format!("could not parse license: {}", line))?;
            packages.push(Package::new(words[0], license));
        }

        Ok(packages)
    }
}

fn parens_balanced(text: &str) -> bool {
    let mut depth = 0;

    for c in text.chars() {
        match c {
            '(' => depth += 1,
            ')' => {
                if depth == 0 {
                    return false;
                } else {
                    depth -= 1
                }
            }
            _ => {}
        }
    }

    return depth == 0
}

fn unparenthesize(text: &str) -> &str {
    let opening_parens = text.chars()
                             .take_while(|c| { *c == '(' })
                             .count();
    let closing_parens = text.chars()
                             .rev()
                             .take_while(|c| { *c == ')' })
                             .count();
    let chars_to_trim = min(opening_parens, closing_parens);
    &text[chars_to_trim..text.len() - chars_to_trim]
}

#[test]
fn test_unparenthesize() {
    assert_eq!("", unparenthesize(""));
    assert_eq!("a", unparenthesize("a"));
    assert_eq!("a", unparenthesize("(a)"));
    assert_eq!("a", unparenthesize("(((a)))"));
    assert_eq!("(a", unparenthesize("(((a))"));
    assert_eq!("a)", unparenthesize("((a)))"));
    assert_eq!(" (a)))", unparenthesize(" (a)))"));
}

#[derive(Debug)]
enum License {
    License(String),
    Or(Vec<License>),
    And(Vec<License>),
}

fn find_paren_end(text: &str) -> Result<usize> {
    assert!(text.chars().next() == Some('('));

    let mut depth = 1;
    for (idx, c) in text.chars().enumerate().skip(1) {
        match c {
            '(' => depth += 1,
            ')' => {
                depth -= 1;
                if depth == 0 {
                    return Ok(idx + 1);
                }
            }
            _ => {}
        }
    }

    Err(Error::from(format!("mismatched opening paren in string: {}", text)))
}

#[derive(Debug)]
enum Separator { Or, And }

fn detect_separator(text: &str) -> Result<Option<Separator>> {
    let mut separator = None;
    let regex = Regex::new(r"(?: or )|(?: and )|[()]")?;

    let mut offset = 0;
    while let Some(m) = regex.find(&text[offset..]) {
        match m.as_str() {
            " or " => {
                match separator {
                    Some(Separator::And) =>  {
                        return Err(Error::from(format!("mismatched separators (and/or) in segment: {}", text)));
                    },
                    _ => separator = Some(Separator::Or)
                }
            },
            " and " => {
                match separator {
                    Some(Separator::Or) => {
                        return Err(Error::from(format!("mismatched separators (and/or) in segment: {}", text)));
                    },
                    _ => separator = Some(Separator::And)
                }
            },
            "(" => { 
                offset += find_paren_end(&text[offset..])? - m.end(); // TODO: hax
            },
            ")" => {
                return Err(Error::from(format!("mismatched closing paren at offset {}, text = {}", offset, text)))
            }
            _ => panic!("should never happen")
        }

        offset += m.end();
    }

    Ok(separator)
}

impl License {
    fn make_or(def: &str) -> Result<License> {
        let mut segments = Vec::new();
        for segment in def.split(" or ") {
            segments.push(License::parse(segment)?);
        }
        Ok(License::Or(segments))
    }

    fn make_and(def: &str) -> Result<License> {
        let mut segments = Vec::new();
        for segment in def.split(" and ") {
            segments.push(License::parse(segment)?);
        }
        Ok(License::And(segments))
    }

    fn parse(raw_text: &str) -> Result<License> {
        let text = unparenthesize(raw_text.trim());

        if text.is_empty() {
            Err(Error::from("invalid empty license description segment"))
        } else {
            match detect_separator(text)? {
                Some(Separator::Or) => License::make_or(text),
                Some(Separator::And) => License::make_and(text),
                None => {
                    if parens_balanced(text) {
                        Ok(License::License(text.to_owned()))
                    } else {
                        Err(Error::from(format!("unbalanced parentheses in segment: {}", text)))
                    }
                }
            }
        }
    }

    fn matches(&self, good_licenses: &HashSet<String>) -> bool {
        match self {
            License::License(name) => good_licenses.contains(name),
            License::Or(sub_licenses) => {
                sub_licenses.iter().any(|l| { l.matches(good_licenses) })
            },
            License::And(sub_licenses) => {
                sub_licenses.iter().all(|l| { l.matches(good_licenses) })
            }
        }
    }
}

impl PartialEq for License {
    fn eq(&self, other: &License) -> bool {
        match (self, other) {
            (License::License(a), License::License(b)) => a == b,
            (License::Or(a), License::Or(b)) => a == b,
            (License::And(a), License::And(b)) => a == b,
            _ => false
        }
    }
}

#[test]
fn license_parse_trivial() {
    assert_eq!(License::License("trivial".to_owned()),
               License::parse("trivial").unwrap());
    assert_eq!(License::License("with spaces".to_owned()),
               License::parse("with spaces").unwrap());
    assert_eq!(License::License("spaces around".to_owned()),
               License::parse("  spaces around\t\n").unwrap());
    assert_eq!(License::License("parens around".to_owned()),
               License::parse("(parens around)").unwrap());
}

#[test]
fn license_parse_or() {
    assert_eq!(License::Or(
                   vec!(License::License("a".to_owned()),
                        License::License("b".to_owned()))),
               License::parse("a or b").unwrap());
    assert_eq!(License::Or(
                   vec!(License::License("a".to_owned()),
                        License::License("b".to_owned()),
                        License::License("c".to_owned()))),
               License::parse("a or b or c").unwrap());
}

#[test]
fn license_parse_and() {
    assert_eq!(License::And(
                   vec!(License::License("a".to_owned()),
                        License::License("b".to_owned()))),
               License::parse("a and b").unwrap());
    assert_eq!(License::And(
                   vec!(License::License("a".to_owned()),
                        License::License("b".to_owned()),
                        License::License("c".to_owned()))),
               License::parse("a and b and c").unwrap());
}

#[test]
fn license_parse_nested() {
    assert_eq!(License::Or(
                   vec!(License::And(vec!(License::License("a".to_owned()),
                                          License::License("b".to_owned()))),
                        License::License("c".to_owned()))),
               License::parse("(a and b) or c").unwrap());
    assert_eq!(License::Or(
                   vec!(License::License("a".to_owned()),
                        License::And(vec!(License::License("b".to_owned()),
                                          License::License("c".to_owned()))))),
               License::parse("a or (b and c)").unwrap());
    assert_eq!(License::And(
                   vec!(License::Or(vec!(License::License("a".to_owned()),
                                         License::License("b".to_owned()))),
                        License::License("c".to_owned()))),
               License::parse("(a or b) and c").unwrap());
    assert_eq!(License::And(
                   vec!(License::License("a".to_owned()),
                        License::Or(vec!(License::License("b".to_owned()),
                                         License::License("c".to_owned()))))),
               License::parse("a and (b or c)").unwrap());
    assert_eq!(License::And(
                   vec!(License::Or(vec!(License::License("a".to_owned()),
                                         License::License("b".to_owned()))),
                        License::Or(vec!(License::License("c".to_owned()),
                                         License::License("f".to_owned()))))),
               License::parse("(a or b) and (c or d)").unwrap());
}

#[test]
fn license_parse_invalid() {
    assert_matches!(License::parse(""), Err(_));
    assert_matches!(License::parse("("), Err(_));
    assert_matches!(License::parse(")"), Err(_));
    assert_matches!(License::parse("(a"), Err(_));
    assert_matches!(License::parse("a)"), Err(_));
    assert_matches!(License::parse(" (a"), Err(_));
    assert_matches!(License::parse("a) "), Err(_));
    assert_matches!(License::parse("((a)"), Err(_));
    assert_matches!(License::parse("(a))"), Err(_));
    assert_matches!(License::parse("a and b or c"), Err(_));
    assert_matches!(License::parse("a or b and c"), Err(_));
}

fn main() {
    let licenses = match read_licenses_from_file("good-licences.txt") {
        Ok(licenses) => licenses,
        Err(e) => {
            eprintln!("{}", e);
            process::exit(1)
        }
    };

    let packages = match PackageReader::default().read_packages() {
        Ok(packages) => packages,
        Err(e) => {
            eprintln!("{}", e);
            process::exit(1)
        }
    };

    for package in packages {
        if package.license.matches(&licenses) {
            println!("{}: zajebioza", package.name);
        } else {
            println!("{}: chujowo", package.name);
        }
    }
}
