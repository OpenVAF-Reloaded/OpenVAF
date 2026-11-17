use std::fmt::Display;

use hir::{Node, Parameter};
use lasso::Spur;
use mir::{FunctionSignature, Param};
use stdx::Ieee64;

use crate::fmt::{DisplayKind, FmtArg};
use crate::LimitState;

#[derive(Debug, Clone, Copy, Hash, Eq, PartialEq)]
pub enum ParamInfoKind {
    Invalid,
    MinInclusive,
    MaxInclusive,
    MinExclusive,
    MaxExclusive,
}

#[derive(Debug, Clone, Hash, Eq, PartialEq)]
pub enum RetFlag {
    Abort,
    Finish,
    Stop,
    Limited,
}

impl std::fmt::Display for RetFlag {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let txt = match self {
            Self::Abort => "abort",
            Self::Finish => "finish",
            Self::Stop => "stop",
            Self::Limited => "limited",
        };
        write!(f, "{}", txt)
    }
}

#[derive(Debug, Clone, Hash, Eq, PartialEq)]
pub enum CallBackKind {
    Print {
        kind: DisplayKind,
        arg_tys: Box<[FmtArg]>,
    },
    SimParam,
    SimParamOpt,
    SimParamStr,
    Derivative(Param),
    NodeDerivative(Node),
    ParamInfo(ParamInfoKind, Parameter),
    CollapseHint(Node, Option<Node>),
    /// `$discontinuity(i)`: -1 inside a `$limit` function sets the limiting flag,
    /// other negative values are ignored, nonnegative values update the
    /// discontinuity slot
    Discontinuity {
        in_limit: bool,
    },
    Analysis,
    BuiltinLimit {
        name: Spur,
        num_args: u32,
    },
    StoreLimit(LimitState),
    TimeDerivative,
    WhiteNoise {
        name: Spur,
        idx: u32,
    },
    FlickerNoise {
        name: Spur,
        idx: u32,
    },
    NoiseTable(Box<NoiseTable>),
    SetRetFlag(RetFlag),
    /// Next state of a random number generator (`<prefix>_next` in stdlib, see
    /// [`RandomGen::prefix`]). Takes the state followed by the generator arguments.
    RandomNext {
        gen: RandomGen,
        ieee1364: bool,
    },
    /// Value generated when advancing from a generator state (`<prefix>_value` in
    /// stdlib), takes the same (old) state and arguments as `RandomNext`
    RandomValue {
        gen: RandomGen,
        ieee1364: bool,
    },
}

/// Random number generator of a `RandomNext`/`RandomValue` callback
#[derive(Debug, Clone, Copy, Hash, Eq, PartialEq)]
pub enum RandomGen {
    /// `$random`, `$arandom`
    Random,
    /// `$dist_uniform(seed, start, end)`
    UniformInt,
    /// `$dist_normal(seed, mean, standard_deviation)`
    NormalInt,
    /// `$dist_exponential(seed, mean)`
    ExponentialInt,
    /// `$dist_poisson(seed, mean)`
    PoissonInt,
    /// `$dist_chi_square(seed, degree_of_freedom)`
    ChiSquareInt,
    /// `$dist_t(seed, degree_of_freedom)`
    TInt,
    /// `$dist_erlang(seed, k_stage, mean)`
    ErlangInt,
    /// `$rdist_uniform(seed, start, end)`
    UniformReal,
    /// `$rdist_normal(seed, mean, standard_deviation)`
    NormalReal,
    /// `$rdist_exponential(seed, mean)`
    ExponentialReal,
    /// `$rdist_poisson(seed, mean)`
    PoissonReal,
    /// `$rdist_chi_square(seed, degree_of_freedom)`
    ChiSquareReal,
    /// `$rdist_t(seed, degree_of_freedom)`
    TReal,
    /// `$rdist_erlang(seed, k_stage, mean)`
    ErlangReal,
}

impl RandomGen {
    /// Prefix of the stdlib functions (`<prefix>_next`, `<prefix>_value`)
    pub fn prefix(self, ieee1364: bool) -> &'static str {
        match (self, ieee1364) {
            (RandomGen::Random, false) => "vams_random",
            (RandomGen::Random, true) => "vams_random_ieee",
            (RandomGen::UniformInt, false) => "vams_uniform_int",
            (RandomGen::UniformInt, true) => "vams_uniform_int_ieee",
            (RandomGen::NormalInt, false) => "vams_normal_int",
            (RandomGen::NormalInt, true) => "vams_normal_int_ieee",
            (RandomGen::ExponentialInt, false) => "vams_exponential_int",
            (RandomGen::ExponentialInt, true) => "vams_exponential_int_ieee",
            (RandomGen::PoissonInt, false) => "vams_poisson_int",
            (RandomGen::PoissonInt, true) => "vams_poisson_int_ieee",
            (RandomGen::ChiSquareInt, false) => "vams_chi_square_int",
            (RandomGen::ChiSquareInt, true) => "vams_chi_square_int_ieee",
            (RandomGen::TInt, false) => "vams_t_int",
            (RandomGen::TInt, true) => "vams_t_int_ieee",
            (RandomGen::ErlangInt, false) => "vams_erlang_int",
            (RandomGen::ErlangInt, true) => "vams_erlang_int_ieee",
            (RandomGen::UniformReal, false) => "vams_uniform_real",
            (RandomGen::UniformReal, true) => "vams_uniform_real_ieee",
            (RandomGen::NormalReal, false) => "vams_normal_real",
            (RandomGen::NormalReal, true) => "vams_normal_real_ieee",
            (RandomGen::ExponentialReal, false) => "vams_exponential_real",
            (RandomGen::ExponentialReal, true) => "vams_exponential_real_ieee",
            (RandomGen::PoissonReal, false) => "vams_poisson_real",
            (RandomGen::PoissonReal, true) => "vams_poisson_real_ieee",
            (RandomGen::ChiSquareReal, false) => "vams_chi_square_real",
            (RandomGen::ChiSquareReal, true) => "vams_chi_square_real_ieee",
            (RandomGen::TReal, false) => "vams_t_real",
            (RandomGen::TReal, true) => "vams_t_real_ieee",
            (RandomGen::ErlangReal, false) => "vams_erlang_real",
            (RandomGen::ErlangReal, true) => "vams_erlang_real_ieee",
        }
    }

    /// Number of arguments after the state
    pub fn num_args(self) -> u16 {
        match self {
            RandomGen::Random => 0,
            RandomGen::ExponentialInt
            | RandomGen::PoissonInt
            | RandomGen::ChiSquareInt
            | RandomGen::TInt
            | RandomGen::ExponentialReal
            | RandomGen::PoissonReal
            | RandomGen::ChiSquareReal
            | RandomGen::TReal => 1,
            RandomGen::UniformInt
            | RandomGen::NormalInt
            | RandomGen::ErlangInt
            | RandomGen::UniformReal
            | RandomGen::NormalReal
            | RandomGen::ErlangReal => 2,
        }
    }

    /// Whether the arguments after the state and the value are real (otherwise
    /// integer). The state is always an integer.
    pub fn is_real(self) -> bool {
        matches!(
            self,
            RandomGen::UniformReal
                | RandomGen::NormalReal
                | RandomGen::ExponentialReal
                | RandomGen::PoissonReal
                | RandomGen::ChiSquareReal
                | RandomGen::TReal
                | RandomGen::ErlangReal
        )
    }
}

impl CallBackKind {
    pub fn signature(&self) -> FunctionSignature {
        match self {
            CallBackKind::SimParam => FunctionSignature {
                name: "simparam".to_owned(),
                params: 1,
                returns: 1,
                has_sideeffects: false,
            },
            CallBackKind::SimParamOpt => FunctionSignature {
                name: "simparam_opt".to_owned(),
                params: 2,
                returns: 1,
                has_sideeffects: false,
            },
            CallBackKind::SimParamStr => FunctionSignature {
                name: "simparam_str".to_owned(),
                params: 1,
                returns: 1,
                has_sideeffects: false,
            },
            CallBackKind::Derivative(param) => FunctionSignature {
                name: format!("ddx_{}", param),
                params: 1,
                returns: 1,
                has_sideeffects: false,
            },
            CallBackKind::NodeDerivative(node) => FunctionSignature {
                name: format!("ddx_node_{:?}", node),
                params: 1,
                returns: 1,
                has_sideeffects: false,
            },
            CallBackKind::ParamInfo(kind, param) => FunctionSignature {
                name: format!("set_{:?}({:?})", kind, param),
                params: 0,
                returns: 0,
                has_sideeffects: true,
            },
            CallBackKind::CollapseHint(hi, lo) => FunctionSignature {
                name: format!("collapse_{:?}_{:?}", hi, lo),
                params: 0,
                returns: 0,
                has_sideeffects: true,
            },
            CallBackKind::Print { kind, arg_tys: args } => FunctionSignature {
                name: format!("{:?})", kind),
                params: args.len() as u16 + 1,
                returns: 0,
                has_sideeffects: true,
            },
            CallBackKind::BuiltinLimit { name, num_args } => FunctionSignature {
                name: format!("$limit[{name:?}]"),
                params: *num_args as u16,
                returns: 1,
                has_sideeffects: false,
            },
            CallBackKind::StoreLimit(state) => FunctionSignature {
                name: format!("$store[{state:?}]"),
                params: 1,
                returns: 1,
                has_sideeffects: false,
            },
            CallBackKind::Discontinuity { in_limit } => FunctionSignature {
                name: if *in_limit { "$discontinuity[lim]" } else { "$discontinuity" }.to_owned(),
                params: 1,
                returns: 0,
                has_sideeffects: true,
            },
            CallBackKind::Analysis => FunctionSignature {
                name: "analysis".to_owned(),
                params: 1,
                returns: 1,
                has_sideeffects: false,
            },
            CallBackKind::TimeDerivative => FunctionSignature {
                name: "ddt".to_string(),
                params: 1,
                returns: 1,
                has_sideeffects: false,
            },
            CallBackKind::WhiteNoise { name, .. } => FunctionSignature {
                name: format!("white_noise({name:?})"),
                params: 1,
                returns: 1,
                has_sideeffects: false,
            },
            CallBackKind::FlickerNoise { name, .. } => FunctionSignature {
                name: format!("flickr_noise({name:?})"),
                params: 2,
                returns: 1,
                has_sideeffects: false,
            },
            CallBackKind::NoiseTable(table) => FunctionSignature {
                name: format!(
                    "table_noise{}({:?}, {:?})",
                    if table.log { "lob" } else { "" },
                    table.name,
                    &table.vals
                ),
                params: 1,
                returns: 1,
                has_sideeffects: false,
            },
            CallBackKind::SetRetFlag(flag) => FunctionSignature {
                name: format!("SetRetFlag[{}]", flag),
                params: 0,
                returns: 0,
                has_sideeffects: true,
            },
            CallBackKind::RandomNext { gen, ieee1364 } => FunctionSignature {
                name: format!("{}_next", gen.prefix(*ieee1364)),
                params: 1 + gen.num_args(),
                returns: 1,
                has_sideeffects: false,
            },
            CallBackKind::RandomValue { gen, ieee1364 } => FunctionSignature {
                name: format!("{}_value", gen.prefix(*ieee1364)),
                params: 1 + gen.num_args(),
                returns: 1,
                has_sideeffects: false,
            },
        }
    }
    pub fn is_noise(&self) -> bool {
        matches!(
            self,
            CallBackKind::WhiteNoise { .. }
                | CallBackKind::FlickerNoise { .. }
                | CallBackKind::NoiseTable(_)
        )
    }

    pub fn op_dependent(&self) -> bool {
        matches!(
            self,
            CallBackKind::SimParam
                | CallBackKind::SimParamOpt
                | CallBackKind::StoreLimit(_)
                | CallBackKind::Analysis
                | CallBackKind::SimParamStr
                | CallBackKind::Discontinuity { .. }
                | CallBackKind::BuiltinLimit { .. }
        )
    }

    pub fn ignore_if_op_dependent(&self) -> bool {
        matches!(self, CallBackKind::CollapseHint(_, _))
    }

    pub fn tracked(&self) -> bool {
        !matches!(self, CallBackKind::Print { .. })
    }
}

#[derive(Debug, Clone, Hash, Eq, PartialEq)]
pub struct NoiseTable {
    pub name: Spur,
    pub log: bool,
    pub vals: Box<[(Ieee64, Ieee64)]>,
    idx: u32,
}

impl NoiseTable {
    // TODO: read from disk
    pub fn new(
        vals: impl IntoIterator<Item = (f64, f64)>,
        log: bool,
        name: Spur,
        idx: u32,
    ) -> Self {
        let mut vals: Vec<(Ieee64, Ieee64)> = if log {
            vals.into_iter().map(|(f, pwr)| (f.into(), pwr.into())).collect()
        } else {
            vals.into_iter().map(|(f, pwr)| (f.log10().into(), pwr.into())).collect()
        };
        vals.sort_unstable_by(|(f1, _), (f2, _)| f1.partial_cmp(f2).unwrap());
        vals.dedup_by_key(|(f, _)| *f);
        Self { name, log, vals: vals.into_boxed_slice(), idx }
    }
}
