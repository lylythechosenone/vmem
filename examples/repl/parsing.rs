use clap::{Parser, ValueEnum};
use clap_num::maybe_hex;
use vmem::AllocPolicy;

#[derive(ValueEnum, Clone, Copy, Debug, Default)]
pub enum Policy {
    #[default]
    Instant,
    Best,
    Next,
}
impl From<Policy> for AllocPolicy {
    fn from(val: Policy) -> Self {
        match val {
            Policy::Instant => AllocPolicy::InstantFit,
            Policy::Best => AllocPolicy::BestFit,
            Policy::Next => AllocPolicy::NextFit,
        }
    }
}

#[derive(Parser, Debug)]
#[command(disable_help_flag = true)]
pub enum Command {
    Create {
        #[arg(long)]
        name: String,
        #[arg(long, value_parser=maybe_hex::<usize>)]
        quantum: usize,
    },
    Delete {
        #[arg(long)]
        arena: String,
    },
    AddSpan {
        #[arg(long)]
        arena: String,
        #[arg(long, value_parser=maybe_hex::<usize>)]
        base: usize,
        #[arg(long, value_parser=maybe_hex::<usize>)]
        size: usize,
    },
    Alloc {
        #[arg(long)]
        arena: String,

        #[arg(long, default_value = "instant")]
        policy: Policy,

        #[arg(long, value_parser=maybe_hex::<usize>)]
        size: usize,
        #[arg(long, value_parser=maybe_hex::<usize>)]
        align: usize,

        #[arg(long, value_parser=maybe_hex::<usize>)]
        phase: Option<usize>,
        #[arg(long, value_parser=maybe_hex::<usize>)]
        nocross: Option<usize>,
        #[arg(long, value_parser=maybe_hex::<usize>)]
        min: Option<usize>,
        #[arg(long, value_parser=maybe_hex::<usize>)]
        max: Option<usize>,
    },
    Free {
        #[arg(long)]
        arena: String,

        #[arg(long, value_parser=maybe_hex::<usize>)]
        base: usize,
    },
    Print {
        #[arg(long)]
        arena: Option<String>,
    },

    Exit,
}
