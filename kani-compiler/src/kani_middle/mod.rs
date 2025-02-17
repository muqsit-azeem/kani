// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! This module contains code that are backend agnostic. For example, MIR analysis
//! and transformations.

use std::collections::HashSet;
use std::path::Path;

use crate::kani_queries::QueryDb;
use rustc_hir::{def::DefKind, def_id::LOCAL_CRATE};
use rustc_middle::mir::write_mir_pretty;
use rustc_middle::span_bug;
use rustc_middle::ty::layout::{
    FnAbiError, FnAbiOf, FnAbiOfHelpers, FnAbiRequest, HasParamEnv, HasTyCtxt, LayoutError,
    LayoutOfHelpers, TyAndLayout,
};
use rustc_middle::ty::{self, Instance as InstanceInternal, Ty as TyInternal, TyCtxt};
use rustc_session::config::OutputType;
use rustc_smir::rustc_internal;
use rustc_span::source_map::respan;
use rustc_span::Span;
use rustc_target::abi::call::FnAbi;
use rustc_target::abi::{HasDataLayout, TargetDataLayout};
use stable_mir::mir::mono::{Instance, InstanceKind, MonoItem};
use stable_mir::mir::pretty::pretty_ty;
use stable_mir::ty::{BoundVariableKind, RigidTy, Span as SpanStable, Ty, TyKind};
use stable_mir::visitor::{Visitable, Visitor as TypeVisitor};
use stable_mir::{CrateDef, DefId};
use std::fs::File;
use std::io::BufWriter;
use std::io::Write;

use self::attributes::KaniAttributes;

pub mod analysis;
pub mod attributes;
pub mod coercion;
mod intrinsics;
pub mod metadata;
pub mod provide;
pub mod reachability;
pub mod resolve;
pub mod stubbing;

/// Check that all crate items are supported and there's no misconfiguration.
/// This method will exhaustively print any error / warning and it will abort at the end if any
/// error was found.
pub fn check_crate_items(tcx: TyCtxt, ignore_asm: bool) {
    let krate = tcx.crate_name(LOCAL_CRATE);
    for item in tcx.hir_crate_items(()).items() {
        let def_id = item.owner_id.def_id.to_def_id();
        KaniAttributes::for_item(tcx, def_id).check_attributes();
        if tcx.def_kind(def_id) == DefKind::GlobalAsm {
            if !ignore_asm {
                let error_msg = format!(
                    "Crate {krate} contains global ASM, which is not supported by Kani. Rerun with \
                    `--enable-unstable --ignore-global-asm` to suppress this error \
                    (**Verification results may be impacted**).",
                );
                tcx.dcx().err(error_msg);
            } else {
                tcx.dcx().warn(format!(
                    "Ignoring global ASM in crate {krate}. Verification results may be impacted.",
                ));
            }
        }
    }
    tcx.dcx().abort_if_errors();
}

/// Check that all given items are supported and there's no misconfiguration.
/// This method will exhaustively print any error / warning and it will abort at the end if any
/// error was found.
pub fn check_reachable_items(tcx: TyCtxt, queries: &QueryDb, items: &[MonoItem]) {
    // Avoid printing the same error multiple times for different instantiations of the same item.
    let mut def_ids = HashSet::new();
    for item in items.iter().filter(|i| matches!(i, MonoItem::Fn(..) | MonoItem::Static(..))) {
        let def_id = match item {
            MonoItem::Fn(instance) => instance.def.def_id(),
            MonoItem::Static(def) => def.def_id(),
            MonoItem::GlobalAsm(_) => {
                unreachable!()
            }
        };
        if !def_ids.contains(&def_id) {
            // Check if any unstable attribute was reached.
            KaniAttributes::for_item(tcx, rustc_internal::internal(def_id))
                .check_unstable_features(&queries.args().unstable_features);
            def_ids.insert(def_id);
        }

        // We don't short circuit here since this is a type check and can shake
        // out differently depending on generic parameters.
        if let MonoItem::Fn(instance) = item {
            if attributes::is_function_contract_generated(tcx, rustc_internal::internal(def_id)) {
                check_is_contract_safe(tcx, *instance);
            }
        }
    }
    tcx.dcx().abort_if_errors();
}

/// A basic check that ensures a function with a contract does not receive
/// mutable pointers in its input and does not return raw pointers of any kind.
///
/// This is a temporary safety measure because contracts cannot yet reason
/// about the heap.
fn check_is_contract_safe(tcx: TyCtxt, instance: Instance) {
    struct NoMutPtr<'tcx> {
        tcx: TyCtxt<'tcx>,
        is_prohibited: fn(Ty) -> bool,
        /// Where (top level) did the type we're analyzing come from. Used for
        /// composing error messages.
        r#where: &'static str,
        /// Adjective to describe the kind of pointer we're prohibiting.
        /// Essentially `is_prohibited` but in English.
        what: &'static str,
    }

    impl<'tcx> TypeVisitor for NoMutPtr<'tcx> {
        type Break = ();
        fn visit_ty(&mut self, ty: &Ty) -> std::ops::ControlFlow<Self::Break> {
            if (self.is_prohibited)(*ty) {
                // TODO make this more user friendly
                self.tcx.dcx().err(format!(
                    "{} contains a {}pointer ({}). This is prohibited for functions with contracts, \
                    as they cannot yet reason about the pointer behavior.", self.r#where, self.what,
                    pretty_ty(ty.kind())));
            }

            // Rust's type visitor only recurses into type arguments, (e.g.
            // `generics` in this match). This is enough for many types, but it
            // won't look at the field types of structs or enums. So we override
            // it here and do that ourselves.
            //
            // Since the field types also must contain in some form all the type
            // arguments the visitor will see them as it inspects the fields and
            // we don't need to call back to `super`.
            if let TyKind::RigidTy(RigidTy::Adt(adt_def, generics)) = ty.kind() {
                for variant in adt_def.variants() {
                    for field in &variant.fields() {
                        self.visit_ty(&field.ty_with_args(&generics))?;
                    }
                }
                std::ops::ControlFlow::Continue(())
            } else {
                // For every other type.
                ty.super_visit(self)
            }
        }
    }

    fn is_raw_mutable_ptr(ty: Ty) -> bool {
        let kind = ty.kind();
        kind.is_raw_ptr() && kind.is_mutable_ptr()
    }

    fn is_raw_ptr(ty: Ty) -> bool {
        let kind = ty.kind();
        kind.is_raw_ptr()
    }

    // TODO: Replace this with fn_abi.
    // https://github.com/model-checking/kani/issues/1365
    let bound_fn_sig = instance.ty().kind().fn_sig().unwrap();

    for var in &bound_fn_sig.bound_vars {
        if let BoundVariableKind::Ty(t) = var {
            tcx.dcx().span_err(
                rustc_internal::internal(instance.def.span()),
                format!("Found a bound type variable {t:?} after monomorphization"),
            );
        }
    }

    let fn_typ = bound_fn_sig.skip_binder();

    for (input_ty, (is_prohibited, r#where, what)) in fn_typ
        .inputs()
        .iter()
        .copied()
        .zip(std::iter::repeat((is_raw_mutable_ptr as fn(_) -> _, "This argument", "mutable ")))
        .chain([(fn_typ.output(), (is_raw_ptr as fn(_) -> _, "The return", ""))])
    {
        let mut v = NoMutPtr { tcx, is_prohibited, r#where, what };
        v.visit_ty(&input_ty);
    }
}

/// Print MIR for the reachable items if the `--emit mir` option was provided to rustc.
pub fn dump_mir_items(tcx: TyCtxt, items: &[MonoItem], output: &Path) {
    /// Convert MonoItem into a DefId.
    /// Skip stuff that we cannot generate the MIR items.
    fn visible_item(item: &MonoItem) -> Option<(MonoItem, DefId)> {
        match item {
            // Exclude FnShims and others that cannot be dumped.
            MonoItem::Fn(instance) if matches!(instance.kind, InstanceKind::Item) => {
                Some((item.clone(), instance.def.def_id()))
            }
            MonoItem::Fn(..) => None,
            MonoItem::Static(def) => Some((item.clone(), def.def_id())),
            MonoItem::GlobalAsm(_) => None,
        }
    }

    if tcx.sess.opts.output_types.contains_key(&OutputType::Mir) {
        // Create output buffer.
        let out_file = File::create(output).unwrap();
        let mut writer = BufWriter::new(out_file);

        // For each def_id, dump their MIR
        for (item, def_id) in items.iter().filter_map(visible_item) {
            writeln!(writer, "// Item: {item:?}").unwrap();
            write_mir_pretty(tcx, Some(rustc_internal::internal(def_id)), &mut writer).unwrap();
        }
    }
}

/// Structure that represents the source location of a definition.
/// TODO: Use `InternedString` once we move it out of the cprover_bindings.
/// <https://github.com/model-checking/kani/issues/2435>
pub struct SourceLocation {
    pub filename: String,
    pub start_line: usize,
    pub start_col: usize,
    pub end_line: usize,
    pub end_col: usize,
}

impl SourceLocation {
    pub fn new(span: SpanStable) -> Self {
        let loc = span.get_lines();
        let filename = span.get_filename().to_string();
        let start_line = loc.start_line;
        let start_col = loc.start_col;
        let end_line = loc.end_line;
        let end_col = loc.end_col;
        SourceLocation { filename, start_line, start_col, end_line, end_col }
    }
}

/// Get the FnAbi of a given instance with no extra variadic arguments.
/// TODO: Get rid of this. Use instance.fn_abi() instead.
/// <https://github.com/model-checking/kani/issues/1365>
pub fn fn_abi<'tcx>(
    tcx: TyCtxt<'tcx>,
    instance: InstanceInternal<'tcx>,
) -> &'tcx FnAbi<'tcx, TyInternal<'tcx>> {
    let helper = CompilerHelpers { tcx };
    helper.fn_abi_of_instance(instance, ty::List::empty())
}

struct CompilerHelpers<'tcx> {
    tcx: TyCtxt<'tcx>,
}

impl<'tcx> HasParamEnv<'tcx> for CompilerHelpers<'tcx> {
    fn param_env(&self) -> ty::ParamEnv<'tcx> {
        ty::ParamEnv::reveal_all()
    }
}

impl<'tcx> HasTyCtxt<'tcx> for CompilerHelpers<'tcx> {
    fn tcx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }
}

impl<'tcx> HasDataLayout for CompilerHelpers<'tcx> {
    fn data_layout(&self) -> &TargetDataLayout {
        self.tcx.data_layout()
    }
}

impl<'tcx> LayoutOfHelpers<'tcx> for CompilerHelpers<'tcx> {
    type LayoutOfResult = TyAndLayout<'tcx>;

    #[inline]
    fn handle_layout_err(&self, err: LayoutError<'tcx>, span: Span, ty: TyInternal<'tcx>) -> ! {
        span_bug!(span, "failed to get layout for `{}`: {}", ty, err)
    }
}

/// Implement error handling for extracting function ABI information.
impl<'tcx> FnAbiOfHelpers<'tcx> for CompilerHelpers<'tcx> {
    type FnAbiOfResult = &'tcx FnAbi<'tcx, TyInternal<'tcx>>;

    #[inline]
    fn handle_fn_abi_err(
        &self,
        err: FnAbiError<'tcx>,
        span: Span,
        fn_abi_request: FnAbiRequest<'tcx>,
    ) -> ! {
        if let FnAbiError::Layout(LayoutError::SizeOverflow(_)) = err {
            self.tcx.dcx().emit_fatal(respan(span, err))
        } else {
            match fn_abi_request {
                FnAbiRequest::OfFnPtr { sig, extra_args } => {
                    span_bug!(
                        span,
                        "Error: {err:?}\n while running `fn_abi_of_fn_ptr. ({sig}, {extra_args:?})`",
                    );
                }
                FnAbiRequest::OfInstance { instance, extra_args } => {
                    span_bug!(
                        span,
                        "Error: {err:?}\n while running `fn_abi_of_instance. ({instance}, {extra_args:?})`",
                    );
                }
            }
        }
    }
}
