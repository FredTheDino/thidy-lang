use gumdrop::Options;

use sylt::{Args, RustFunction};

fn main() -> Result<(), String> {
    let mut args = Args::parse_args_default_or_exit();
    if args.help {
        println!("{}", Args::usage());
        return Ok(());
    }

    if args.file.is_none() {
        return Err("No file to run".to_string());
    }

    if args.target.is_none() {
        let mut target = args.file.clone().unwrap();
        target.set_extension("rs");
        args.target = Some(target);
    }

    let functions: Vec<(String, RustFunction)> =
        sylt_macro::link!(sylt::dbg as dbg, sylt::push as push, sylt::len as len);

    if let Err(errs) = sylt::run_file(&args, functions) {
        for err in errs.iter() {
            println!("{}", err);
        }
        return Err(format!("{} errors occured.", errs.len()));
    }
    Ok(())
}
