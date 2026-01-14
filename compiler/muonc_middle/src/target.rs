//! Representation of a target.

use std::{
    fmt::{self, Display},
    str::FromStr,
};

use thiserror::Error;

/// A target triple
///
/// ```text
/// Target format: <arch><[sub]>-<sys>-<env> where:
/// - arch = `x86_64`, `x86`, `arm`, `aarch64`, `riscv64`, `riscv32`
/// - sub  = for eg, riscv64 = `imaf`, `g`, `gc`
/// - sys  = `linux`, `windows`, `android`, `macos`, `none`
/// - env  = `gnu`, `msvc`, `elf`, `macho`
/// ```
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct TargetTriple {
    arch: Arch,
    sys: Sys,
    env: Env,
}

const _: () = {
    assert!(
        TargetTriple::try_host().is_some(),
        "cannot compile to host target"
    );
};

impl TargetTriple {
    /// List of all supported targets of the compiler
    pub const SUPPORTED_TARGETS: &[TargetTriple] = &[TargetTriple::X86_64_LINUX_GNU];

    /// `x86_64-linux-gnu` target
    pub const X86_64_LINUX_GNU: TargetTriple = TargetTriple {
        arch: Arch::x86_64,
        sys: Sys::Linux,
        env: Env::Gnu,
    };

    /// Returns the target triplet
    pub const fn try_host() -> Option<TargetTriple> {
        let arch = if cfg!(target_arch = "x86_64") {
            Arch::x86_64
        } else if cfg!(target_arch = "x86") {
            Arch::x86
        } else if cfg!(target_arch = "arm") {
            Arch::arm
        } else if cfg!(target_arch = "aarch64") {
            Arch::aarch64
        } else if cfg!(target_arch = "riscv64") {
            Arch::riscv64
        } else if cfg!(target_arch = "riscv32") {
            Arch::riscv32
        } else {
            return None;
        };

        let sys = if cfg!(target_os = "linux") {
            Sys::Linux
        } else if cfg!(target_os = "windows") {
            Sys::Windows
        } else if cfg!(target_os = "macos") {
            Sys::Macos
        } else {
            Sys::Unknown
        };

        let env = if cfg!(target_env = "gnu") {
            Env::Gnu
        } else if cfg!(target_env = "msvc") {
            Env::Msvc
        } else {
            Env::Unknown
        };

        Some(TargetTriple { arch, sys, env })
    }

    /// Returns the host target, will panic if the target is not supported.
    pub const fn host() -> TargetTriple {
        TargetTriple::try_host().unwrap()
    }

    /// Returns the pointer width of this architecture.
    pub const fn pointer_width(&self) -> PointerWidth {
        self.arch.ptr_width()
    }
}

impl FromStr for TargetTriple {
    type Err = TargetParsingError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut splits = s.split('-');

        let unknown_target = || UnknownTarget {
            target: s.to_string(),
        };

        let arch_s = splits.next().ok_or_else(unknown_target)?;
        let sys_s = splits.next().ok_or_else(unknown_target)?;
        let env_s = splits.next().ok_or_else(unknown_target)?;

        if splits.next().is_some() {
            return Err(unknown_target());
        }

        let arch = match arch_s {
            "x86_64" => Arch::x86_64,
            "x86" => Arch::x86,
            "arm" => Arch::arm,
            "aarch64" => Arch::aarch64,
            _ if arch_s.starts_with("riscv64") => Arch::riscv64,
            _ if arch_s.starts_with("riscv32") => Arch::riscv32,
            _ => {
                return Err(UnknownArch {
                    arch: arch_s.to_string(),
                    target: s.to_string(),
                });
            }
        };

        if arch == Arch::riscv32 || arch == Arch::riscv64 {
            todo!("implement parsing of risc-v's extensions")
        }

        let sys = match sys_s {
            "linux" => Sys::Linux,
            "windows" => Sys::Windows,
            "macos" => Sys::Macos,
            "none" => Sys::Unknown,
            _ => {
                return Err(UnknownSys {
                    sys: sys_s.to_string(),
                    target: s.to_string(),
                });
            }
        };

        let env = match env_s {
            "gnu" => Env::Gnu,
            "msvc" => Env::Msvc,
            _ => {
                return Err(UnknownEnv {
                    env: env_s.to_string(),
                    target: s.to_string(),
                });
            }
        };

        Ok(TargetTriple { arch, sys, env })
    }
}

impl Display for TargetTriple {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}-{}-{}", self.arch, self.sys, self.env)
    }
}

use TargetParsingError::*;

#[derive(Debug, Clone, Error)]
pub enum TargetParsingError {
    /// The target is unknown, use more specific error if possible like,
    /// UnknownArch
    #[error("unknown target: `{target}`, type `muonc --target help` for details")]
    UnknownTarget { target: String },
    /// The architecture in the target triple is unknown
    #[error(
        "unknown architecture `{arch}` in target `{target}`, type `muonc -target help` for details"
    )]
    UnknownArch { arch: String, target: String },
    /// The system in the target triple is unknown
    #[error("unknown system `{sys}` in target `{target}`, type `muonc -target help` for details")]
    UnknownSys { sys: String, target: String },
    /// The environment in the target triple is unknown
    #[error(
        "unknown environment `{env}` in target `{target}`, type `muonc -target help` for details"
    )]
    UnknownEnv { env: String, target: String },
}

/// Architecture with sub architecture
#[allow(non_camel_case_types)]
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Arch {
    x86_64,
    x86,
    arm,
    aarch64,
    riscv32,
    riscv64,
}

impl Arch {
    /// Returns the pointer width of this architecture.
    pub const fn ptr_width(&self) -> PointerWidth {
        use PointerWidth::*;

        match self {
            Arch::x86_64 => U64,
            Arch::x86 => U32,
            Arch::arm => U32,
            Arch::aarch64 => U64,
            Arch::riscv32 => U32,
            Arch::riscv64 => U64,
        }
    }
}

impl Display for Arch {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}",
            match self {
                Arch::x86_64 => "x86_64",
                Arch::x86 => "x86",
                Arch::arm => "arm",
                Arch::aarch64 => "aarch64",
                Arch::riscv32 => "riscv32",
                Arch::riscv64 => "riscv64",
            }
        )
    }
}

/// System
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Sys {
    Linux,
    Windows,
    Macos,
    Unknown,
}

impl Display for Sys {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}",
            match self {
                Sys::Linux => "linux",
                Sys::Windows => "windows",
                Sys::Macos => "macos",
                Sys::Unknown => "unknown",
            }
        )
    }
}

/// Environment
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Env {
    Gnu,
    Msvc,
    Unknown,
}

impl Display for Env {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}",
            match self {
                Env::Gnu => "gnu",
                Env::Msvc => "msvc",
                Env::Unknown => "unknown",
            }
        )
    }
}

/// Width of the pointer for a target, supported: 16 bits, 32 bits, 64 bits.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum PointerWidth {
    U16,
    U32,
    U64,
}

impl PointerWidth {
    /// Returns the size of the pointer in bits.
    pub const fn size_bits(&self) -> u8 {
        match self {
            Self::U16 => 16,
            Self::U32 => 32,
            Self::U64 => 64,
        }
    }

    /// Returns the size of the pointer in bytes.
    pub const fn size_bytes(&self) -> u8 {
        match self {
            Self::U16 => 2,
            Self::U32 => 4,
            Self::U64 => 8,
        }
    }

    /// Returns the alignment of the pointer in bytes.
    pub const fn align(&self) -> u32 {
        match self {
            Self::U16 => 2,
            Self::U32 => 4,
            Self::U64 => 8,
        }
    }
}
