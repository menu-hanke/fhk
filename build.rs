use core::str;
use std::process::Command;

fn main() {
    if let Ok(output) = Command::new("git")
        .arg("rev-parse")
        .arg("--short")
        .arg("HEAD")
        .output()
    {
        println!("cargo:rustc-env=FHK_GITHASH={}", str::from_utf8(&output.stdout).unwrap());
    }
}
