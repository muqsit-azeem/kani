// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! This module is for handling Kani intrinsics, i.e. items whose implementation
//! is defined in the Kani compiler. These items are defined in the `kani`
//! library and are annotated with a `rustc_diagnostic_item`.

use super::lean_ctx::FunctionCtx;

use lean_ast::lean_program::{Expr, Stmt, Theorem, Parameter};
use rustc_middle::mir::{BasicBlock, Place};
use rustc_middle::ty::{Instance, TyCtxt};
use rustc_span::Span;
use std::str::FromStr;
use strum::VariantNames;
use strum_macros::{EnumString, EnumVariantNames};
use tracing::debug;
use lean_ast::lean_program::Stmt::Thm;

// TODO: move this enum up to `kani_middle`
#[derive(Debug, Clone, PartialEq, Eq, EnumString, EnumVariantNames)]
pub enum KaniIntrinsic {
    /// Kani assert statement (`kani::assert`)
    KaniAssert,

    /// Kani assume statement (`kani::assume`)
    KaniAssume,
}

/// If provided function is a Kani intrinsic (e.g. assert, assume, cover), returns it
// TODO: move this function up to `kani_middle` along with the enum
pub fn get_kani_intrinsic<'tcx>(
    tcx: TyCtxt<'tcx>,
    instance: Instance<'tcx>,
) -> Option<KaniIntrinsic> {
    for intrinsic in KaniIntrinsic::VARIANTS {
        let attr_sym = rustc_span::symbol::Symbol::intern(intrinsic);
        if let Some(attr_id) = tcx.all_diagnostic_items(()).name_to_id.get(&attr_sym) {
            if instance.def.def_id() == *attr_id {
                debug!("matched: {:?} {:?}", attr_id, attr_sym);
                return Some(KaniIntrinsic::from_str(intrinsic).unwrap());
            }
        }
    }
    None
}

//todo: Clarify this again
impl<'a, 'tcx> FunctionCtx<'a, 'tcx> {
    pub fn codegen_kani_intrinsic(
        &self,
        intrinsic: KaniIntrinsic,
        instance: Instance<'tcx>,
        fargs: Vec<Expr>,
        assign_to: Place<'tcx>,
        target: Option<BasicBlock>,
        span: Option<Span>,
    ) -> (Stmt | Paramertr)
    //todo: (None, Hypothesis) or (Theorem, None) or both
    {
        match intrinsic {
            KaniIntrinsic::KaniAssert => {
                self.codegen_kani_assert(instance, fargs, assign_to, target, span)
            }
            KaniIntrinsic::KaniAssume => {
                self.codegen_kani_assume(instance, fargs, assign_to, target, span)
            }
        }
    }

    pub fn codegen_kani_assert(
        &self,
        _instance: Instance<'tcx>,
        mut _fargs: Vec<Expr>,
        _assign_to: Place<'tcx>,
        _target: Option<BasicBlock>,
        _span: Option<Span>,
    ) -> Thm {
        Theorem {}
    }

    // TODO: Hypothesis as an input
    pub fn codegen_kani_assume(
        &self,
        _instance: Instance<'tcx>,
        mut _fargs: Vec<Expr>,
        _assign_to: Place<'tcx>,
        _target: Option<BasicBlock>,
        _span: Option<Span>,
    ) -> Parameter{
        Parameter{ name: "h".to_string(), typ: Type::Bool }
    }
}
