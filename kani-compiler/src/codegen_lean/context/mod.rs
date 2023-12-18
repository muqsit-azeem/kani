// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! This module hosts the context used by Kani to convert MIR into Lean.  See
//! the file level comments for more details.

mod lean_ctx;
mod kani_intrinsic;

pub use lean_ctx::LeanCtx;