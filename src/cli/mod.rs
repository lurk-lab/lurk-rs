mod loader;
mod prove_and_verify;

use std::fs;
use std::path::PathBuf;

use anyhow::{bail, Result};

use lurk::eval::lang::Coproc;
use lurk::field::{LanguageField, LurkField};
use lurk::store::Store;
use lurk::z_data::{from_z_data, ZData};
use lurk::z_store::ZStore;
use pasta_curves::{pallas, vesta};

use clap::{Args, Parser, Subcommand};
use tap::TapOptional;

use self::loader::Loader;
use self::prove_and_verify::verify_proof;

const DEFAULT_FIELD: LanguageField = LanguageField::Pallas;
const DEFAULT_LIMIT: usize = 100_000_000;
const DEFAULT_RC: usize = 1;

#[derive(Parser, Debug)]
#[clap(version, about, long_about = None)]
struct Cli {
    #[clap(subcommand)]
    command: Command,
}

#[derive(Subcommand, Debug)]
enum Command {
    Load(Load),
    Repl(Repl),
    Verify(Verify),
}

#[derive(Args, Debug)]
struct Load {
    #[clap(value_parser)]
    lurk_file: PathBuf,

    #[clap(long, value_parser)]
    zstore: Option<PathBuf>,

    #[clap(long, value_parser)]
    limit: Option<usize>,

    #[arg(long)]
    prove: bool,

    #[clap(long, name = "reduction count", value_parser)]
    rc: Option<usize>,
}

#[derive(Parser, Debug)]
struct LoadCli {
    #[clap(value_parser)]
    lurk_file: PathBuf,

    #[clap(long, value_parser)]
    zstore: Option<PathBuf>,

    #[clap(long, value_parser)]
    limit: Option<usize>,

    #[arg(long)]
    prove: bool,

    #[clap(long, name = "reduction count", value_parser)]
    rc: Option<usize>,
}

impl Load {
    pub fn into_cli(self) -> LoadCli {
        LoadCli {
            lurk_file: self.lurk_file,
            zstore: self.zstore,
            limit: self.limit,
            prove: self.prove,
            rc: self.rc,
        }
    }
}

#[derive(Args, Debug)]
struct Repl {
    #[clap(long, value_parser)]
    load: Option<PathBuf>,

    #[clap(long, value_parser)]
    zstore: Option<PathBuf>,

    #[clap(long, value_parser)]
    limit: Option<usize>,

    #[clap(long, name = "reduction count", value_parser)]
    rc: Option<usize>,
}

#[derive(Parser, Debug)]
struct ReplCli {
    #[clap(long, value_parser)]
    load: Option<PathBuf>,

    #[clap(long, value_parser)]
    zstore: Option<PathBuf>,

    #[clap(long, value_parser)]
    limit: Option<usize>,

    #[clap(long, name = "reduction count", value_parser)]
    rc: Option<usize>,
}

impl Repl {
    pub fn into_cli(self) -> ReplCli {
        ReplCli {
            load: self.load,
            zstore: self.zstore,
            limit: self.limit,
            rc: self.rc,
        }
    }
}

fn get_field() -> Result<LanguageField> {
    if let Ok(lurk_field) = std::env::var("LURK_FIELD") {
        match lurk_field.to_lowercase().as_str() {
            "bls12-381" => Ok(LanguageField::BLS12_381),
            "pallas" => Ok(LanguageField::Pallas),
            "vesta" => Ok(LanguageField::Vesta),
            _ => bail!("Field not supported: {lurk_field}"),
        }
    } else {
        Ok(DEFAULT_FIELD)
    }
}

fn get_store<F: LurkField + for<'a> serde::de::Deserialize<'a>>(
    zstore: &Option<PathBuf>,
) -> Store<F> {
    zstore
        .as_ref()
        .and_then(|zstore_path| fs::read(zstore_path).ok())
        .and_then(|zstore_bytes| ZData::from_bytes(&zstore_bytes).ok())
        .and_then(|zstore_data| from_z_data(&zstore_data).ok())
        .map(|zstore: ZStore<F>| zstore.to_store())
        .tap_none(|| {
            if zstore.is_some() {
                eprintln!("Failed to load ZStore. Starting with empty store.")
            }
        })
        .unwrap_or_default()
}

macro_rules! new_loader {
    ( $cli: expr, $field: path ) => {{
        let limit = $cli.limit.unwrap_or(DEFAULT_LIMIT);
        let rc = $cli.rc.unwrap_or(DEFAULT_RC);
        let mut store = get_store(&$cli.zstore);
        let env = store.nil();
        let loader = Loader::<$field, Coproc<$field>>::new(store, env, limit, rc);
        loader
    }};
}

impl ReplCli {
    pub fn run(&self) -> Result<()> {
        macro_rules! repl {
            ( $field: path ) => {{
                let mut loader = new_loader!(self, $field);
                if let Some(lurk_file) = &self.load {
                    loader.load_file(lurk_file)?;
                }
                loader.repl()
            }};
        }
        match get_field()? {
            LanguageField::Pallas => repl!(pallas::Scalar),
            LanguageField::Vesta => repl!(vesta::Scalar),
            LanguageField::BLS12_381 => repl!(blstrs::Scalar),
        }
    }
}

impl LoadCli {
    pub fn run(&self) -> Result<()> {
        macro_rules! load {
            ( $field: path ) => {{
                let mut loader = new_loader!(self, $field);
                loader.load_file(&self.lurk_file)?;
                if self.prove {
                    loader.prove_last_claim()?;
                }
                Ok(())
            }};
        }
        match get_field()? {
            LanguageField::Pallas => load!(pallas::Scalar),
            LanguageField::Vesta => load!(vesta::Scalar),
            LanguageField::BLS12_381 => load!(blstrs::Scalar),
        }
    }
}

#[derive(Args, Debug)]
struct Verify {
    #[clap(value_parser)]
    proof_file: PathBuf,
}

pub fn parse() -> Result<()> {
    if let Ok(cli) = ReplCli::try_parse() {
        cli.run()
    } else if let Ok(cli) = LoadCli::try_parse() {
        cli.run()
    } else {
        match Cli::parse().command {
            Command::Repl(arg) => arg.into_cli().run(),
            Command::Load(arg) => arg.into_cli().run(),
            Command::Verify(verify) => verify_proof(&verify.proof_file),
        }
    }
}
