use std::fs;
use std::path::Path;
use std::path::PathBuf;
use std::process::Command;

use moria::{evaluate_program_vm, infer_expression_type, parse};

fn try_run_script(bin: &str, path: &Path, args: &[&str]) -> Option<(String, i32)> {
    let out = Command::new(bin).args(args).arg(path).output().ok()?;
    let status = out.status.code().unwrap_or(-1);
    let stdout = String::from_utf8_lossy(&out.stdout).to_string();
    Some((stdout, status))
}

fn is_chez(bin: &str) -> bool {
    // 1) Quick check: version prints something
    if let Ok(out) = Command::new(bin).arg("--version").output() {
        if out.status.success() && (!out.stdout.is_empty() || !out.stderr.is_empty()) {
            return true;
        }
    }

    // 2) Try executing a trivial script
    let probe = "(begin (write \"ok\") (newline))\n";
    let mut path = std::env::temp_dir();
    path.push("moria_chez_probe.scm");
    if fs::write(&path, probe).is_err() {
        return false;
    }

    let arg_patterns: &[&[&str]] = &[&["--script"], &["-q", "--script"], &["-q", "-s"], &["-s"]];
    for args in arg_patterns.iter() {
        if let Some((out, status)) = try_run_script(bin, &path, args) {
            if status == 0 && out.trim() == "ok" {
                return true;
            }
        }
    }
    false
}

fn find_chez() -> Option<String> {
    // 1) Allow override via env var
    if let Ok(bin) = std::env::var("MORIA_CHEZ_BIN") {
        if !bin.is_empty() && is_chez(&bin) {
            return Some(bin);
        }
    }
    // 2) Try common binary names
    let candidates = [
        // typical Chez installs
        "chez",
        "chezscheme",
        "chez-scheme",
        "chezscheme9.5",
        "chezscheme9.6",
        "scheme",
    ];
    for bin in candidates.iter() {
        if is_chez(bin) {
            return Some((*bin).to_string());
        }
    }
    None
}

struct ChezExec {
    stdout: String,
    stderr: String,
    status: i32,
}

fn chez_eval_file_full(bin: &str, file_path: &Path) -> Option<ChezExec> {
    // Read forms from file, evaluate sequentially; if a form is (begin ...), evaluate subforms in order.
    // Capture and print the last value.
    let escaped = file_path
        .to_string_lossy()
        .replace("\\", "\\\\")
        .replace('"', "\\\"");
    let wrapped = format!(
        r#"
      (let* ((p (open-input-file "{FILE}")))
        (define (eval-begin xs)
          (let loop ((ys xs) (last (void)))
            (if (null? ys)
                last
                (loop (cdr ys) (eval (car ys) (interaction-environment))))))
        (define (eval-form f)
          (if (and (pair? f) (eq? (car f) 'begin))
              (eval-begin (cdr f))
              (eval f (interaction-environment))))
        (let rec ((last (void)))
          (let ((x (read p)))
            (if (eof-object? x)
                (begin (close-input-port p) (write last) (newline))
                (rec (eval-form x))))))
    "#,
        FILE = escaped
    );
    let mut path = std::env::temp_dir();
    path.push("moria_chez_eval.scm");
    if fs::write(&path, wrapped).is_err() {
        return None;
    }

    let arg_patterns: &[&[&str]] = &[&["--script"], &["-q", "--script"], &["-q", "-s"], &["-s"]];
    for args in arg_patterns.iter() {
        let out = Command::new(bin).args(*args).arg(&path).output().ok()?;
        let status = out.status.code().unwrap_or(-1);
        let stdout = String::from_utf8_lossy(&out.stdout).to_string();
        let stderr = String::from_utf8_lossy(&out.stderr).to_string();
        if status == 0 && !stdout.trim().is_empty() {
            return Some(ChezExec {
                stdout,
                stderr,
                status,
            });
        }
        // keep last attempt info to report
        if args == arg_patterns.last().unwrap() {
            return Some(ChezExec {
                stdout,
                stderr,
                status,
            });
        }
    }
    None
}

fn moria_eval_file(path: &PathBuf) -> String {
    let src = fs::read_to_string(path).unwrap();
    let program = parse(&src).unwrap();
    let val = evaluate_program_vm(&program).unwrap();
    let last_ty = program
        .expressions
        .last()
        .and_then(|e| infer_expression_type(e).ok());
    match last_ty {
        Some(t) => format!("{} :: {}", val, t),
        None => format!("{}", val),
    }
}

#[test]
fn chez_file_compat_snapshots() {
    let mut dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    dir.push("tests/fixtures/r7rs-minimal");
    let entries = fs::read_dir(&dir).expect("fixtures directory missing");

    let chez_bin = find_chez();

    for entry in entries {
        let entry = entry.unwrap();
        if !entry.file_type().unwrap().is_file() {
            continue;
        }
        let path = entry.path();
        if path.extension().and_then(|s| s.to_str()) != Some("scm") {
            continue;
        }

        let moria_out = moria_eval_file(&path);
        let snapshot_text = if let Some(bin) = chez_bin.clone() {
            if let Some(chez) = chez_eval_file_full(&bin, &path) {
                let chez_out = chez.stdout.trim().to_string();
                if chez.status == 0 && !chez_out.is_empty() {
                    format!(
                        "File: {:?}\nBin  : {}\nMoria: {}\nChez : {}\n",
                        path.file_name().unwrap(),
                        bin,
                        moria_out,
                        chez_out
                    )
                } else {
                    format!("File: {:?}\nBin  : {}\nMoria: {}\nChez : <exec error {}>\nStderr:\n{}\nStdout:\n{}\n", path.file_name().unwrap(), bin, moria_out, chez.status, chez.stderr, chez_out)
                }
            } else {
                format!(
                    "File: {:?}\nBin  : {}\nMoria: {}\nChez : <exec error>\n",
                    path.file_name().unwrap(),
                    bin,
                    moria_out
                )
            }
        } else {
            // Always include a Chez line for consistency even if not found
            format!(
                "File: {:?}\nBin  : <not found>\nMoria: {}\nChez : <not found>\n",
                path.file_name().unwrap(),
                moria_out
            )
        };

        // Use file name as snapshot name for stability
        let name = format!("chez_file_{}", path.file_name().unwrap().to_string_lossy());
        insta::assert_snapshot!(name, snapshot_text);
    }
}
