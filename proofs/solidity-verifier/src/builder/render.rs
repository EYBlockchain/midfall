// SPDX-License-Identifier: CC0-1.0
//! Options-driven rendering entry points for `SolidityGenerator`.

use super::*;
use crate::{
    api::{RenderQuotient, RenderVk},
    lowering::{plan::LoweringPlan, render::Halo2VerifyingKey},
};

struct VerifierRenderPlan {
    separate: bool,
    trace: bool,
    gas_checkpoints: bool,
    quotient: RenderQuotient,
    provenance: Option<[u8; 32]>,
}

impl<'a> SolidityGenerator<'a> {
    /// Render generated Solidity artifacts according to one immutable options
    /// value.
    pub fn render(&self, options: RenderOptions) -> Result<RenderedArtifacts, GeneratorError> {
        let separate = matches!(options.vk, RenderVk::Separate);
        let external_quotient = matches!(options.quotient, RenderQuotient::ExternalPinned { .. });

        let inputs = self.inputs();
        let plan = self.plan()?;

        let render_plan = VerifierRenderPlan {
            separate,
            trace: options.diagnostics.trace,
            gas_checkpoints: options.diagnostics.gas_checkpoints,
            quotient: options.quotient,
            provenance: options.provenance,
        };
        let verifier = self.render_verifier_source_with_plan(&inputs, plan, render_plan)?;

        let verifying_key = separate.then(|| Self::render_vk_model(&plan.vk)).transpose()?;
        let quotient_evaluator = external_quotient
            .then(|| self.render_quotient_evaluator_with_plan(&inputs, plan, options.diagnostics))
            .transpose()?;

        Ok(RenderedArtifacts {
            verifier,
            verifying_key,
            quotient_evaluator,
            feature_profile: crate::feature_profile(),
        })
    }

    /// Render only `Halo2QuotientEvaluator.sol`.
    ///
    /// Pinned-quotient deployment flows compile/deploy this source first,
    /// compute its runtime length and codehash, then render the verifier with
    /// [`RenderQuotient::ExternalPinned`].
    pub fn render_quotient_evaluator(
        &self,
        diagnostics: RenderDiagnostics,
    ) -> Result<String, GeneratorError> {
        let inputs = self.inputs();
        let plan = self.plan()?;
        self.render_quotient_evaluator_with_plan(&inputs, plan, diagnostics)
    }

    /// Render the split quotient evaluator from a caller-provided converged
    /// plan.
    ///
    /// Keeping this helper plan-parameterized prevents the verifier render and
    /// evaluator render from silently planning different memory/quotient facts
    /// inside one `render` call.
    fn render_quotient_evaluator_with_plan(
        &self,
        inputs: &VerifierBuildInputs<'_, '_>,
        plan: &LoweringPlan,
        diagnostics: RenderDiagnostics,
    ) -> Result<String, GeneratorError> {
        let mut quotient_output = String::new();
        inputs
            .generate_quotient_evaluator_from_plan(plan, diagnostics.trace)
            .render(&mut quotient_output)
            .map_err(|err| {
                GeneratorError::planning(
                    "render-model",
                    format!("Halo2QuotientEvaluator.sol: {err}"),
                )
            })?;
        Ok(quotient_output)
    }

    /// Render the main verifier source from the same converged plan.
    ///
    /// [`RenderQuotient::ExternalPinned`] carries the runtime length/codehash
    /// the caller obtained by compiling and deploying the evaluator first.
    fn render_verifier_source_with_plan(
        &self,
        inputs: &VerifierBuildInputs<'_, '_>,
        plan: &LoweringPlan,
        render_plan: VerifierRenderPlan,
    ) -> Result<String, GeneratorError> {
        let mut verifier_output = String::new();
        inputs
            .generate_verifier_from_plan(
                plan,
                render_plan.separate,
                render_plan.trace,
                render_plan.gas_checkpoints,
                render_plan.quotient,
                render_plan.provenance,
            )
            .render(&mut verifier_output)
            .map_err(|err| {
                GeneratorError::planning("render-model", format!("Halo2Verifier.sol: {err}"))
            })?;
        Ok(verifier_output)
    }

    /// Render the separate verifying-key payload contract.
    fn render_vk_model(vk: &Halo2VerifyingKey) -> Result<String, GeneratorError> {
        let mut vk_output = String::new();
        vk.render(&mut vk_output).map_err(|err| {
            GeneratorError::planning("render-model", format!("Halo2VerifyingKey.sol: {err}"))
        })?;
        Ok(vk_output)
    }
}
