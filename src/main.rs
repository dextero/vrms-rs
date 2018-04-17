use std::fmt;
use std::fmt::Display;
use std::error::Error;
use std::fs::File;
use std::io::BufReader;
use std::io::BufRead;
use std::collections::HashSet;
use std::process::Command;
use std::process;

#[derive(Debug)]
struct VrmsError {
    msg: String,
}

impl VrmsError {
    fn new(msg: String) -> VrmsError {
        VrmsError { msg: msg }
    }

    fn new_box(msg: String) -> Box<VrmsError> {
        Box::new(Self::new(msg))
    }
}

impl Display for VrmsError {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        formatter.write_str(self.description())
    }
}

impl Error for VrmsError {
    fn description(&self) -> &str {
        &self.msg
    }
}

type Result<T> = std::result::Result<T, Box<Error>>;

fn read_licences_from_file(file: &str) -> Result<HashSet<String>> {
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
    licence: String
}

impl Package {
    fn new(name: &str, licence: &str) -> Package {
        Package {
            name: name.to_owned(),
            licence: licence.to_owned()
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
            .output()
            .expect("failed to execute process");
        let mut packages = Vec::new();
        let packages_str = String::from_utf8(child.stdout)?;

        for line in packages_str.lines() {
            let words: Vec<&str> = line.split('\t').collect();
            if words.len() != 2 {
                return Err(VrmsError::new_box(format!("unexpected line format: {}", line)));
            }
            packages.push(Package::new(words[0], words[1]));
        }

        Ok(packages)
    }
}

fn main() {
    let licences = match read_licences_from_file("good-licences.txt") {
        Ok(licences) => licences,
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
        if licences.contains(&package.licence) {
            println!("{}: zajebioza", package.name);
        } else {
            println!("{}: chujowo", package.name);
        }
    }
}
