// SPDX-License-Identifier: CC0-1.0
//! Options-driven rendering entry points for `SolidityGenerator`.

use ruint::aliases::U256;

use super::*;
use crate::{
    api::{QuotientLowering, RenderQuotient, RenderVk},
    lowering::{plan::LoweringPlan, render::Halo2VerifyingKey},
};

struct VerifierRenderPlan {
    separate: bool,
    trace: bool,
    gas_checkpoints: bool,
    external_quotient: bool,
    expected_quotient: Option<(usize, U256)>,
    /// Test-only quotient probe (`render_quotient_probe`); `render` never
    /// sets it.
    quotient_probe: bool,
}

impl<'a> SolidityGenerator<'a> {
    /// Render generated Solidity artifacts according to one immutable options
    /// value.
    pub fn render(&self, options: RenderOptions) -> Result<RenderedArtifacts, GeneratorError> {
        let separate = matches!(options.vk, RenderVk::Separate);
        let (external_quotient, expected_quotient) = match options.quotient {
            RenderQuotient::Inline => (false, None),
            RenderQuotient::ExternalPinned {
                runtime_len,
                codehash,
            } => (true, Some((runtime_len, codehash))),
        };

        if options.quotient_lowering == QuotientLowering::Direct && external_quotient {
            return Err(GeneratorError::Planning {
                stage: "quotient lowering",
                message: "QuotientLowering::Direct renders the quotient inline; it cannot be \
                          combined with RenderQuotient::ExternalPinned"
                    .to_string(),
            });
        }

        let inputs = self.inputs();
        let plan = inputs.lowering_plan_for(options.quotient_lowering)?;

        let render_plan = VerifierRenderPlan {
            separate,
            trace: options.diagnostics.trace,
            gas_checkpoints: options.diagnostics.gas_checkpoints,
            external_quotient,
            expected_quotient,
            quotient_probe: false,
        };
        let verifier = self.render_verifier_source_with_plan(&inputs, &plan, render_plan)?;

        let verifying_key = separate.then(|| Self::render_vk_model(&plan.vk)).transpose()?;
        let quotient_evaluator = external_quotient
            .then(|| self.render_quotient_evaluator_with_plan(&inputs, &plan, options.diagnostics))
            .transpose()?;

        Ok(RenderedArtifacts {
            verifier,
            verifying_key,
            quotient_evaluator,
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
        let plan = inputs.lowering_plan();
        self.render_quotient_evaluator_with_plan(&inputs, &plan, diagnostics)
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
            .map_err(|_| GeneratorError::Render {
                artifact: "Halo2QuotientEvaluator.sol",
            })?;
        Ok(quotient_output)
    }

    /// Render the main verifier source from the same converged plan.
    ///
    /// `expected_quotient` is present only after the external evaluator has
    /// been compiled/deployed by the caller and its runtime hash is known.
    fn render_verifier_source_with_plan(
        &self,
        inputs: &VerifierBuildInputs<'_, '_>,
        plan: &LoweringPlan,
        render_plan: VerifierRenderPlan,
    ) -> Result<String, GeneratorError> {
        let mut verifier_output = String::new();
        let mut model = inputs.generate_verifier_from_plan(
            plan,
            render_plan.separate,
            render_plan.trace,
            render_plan.gas_checkpoints,
            render_plan.external_quotient,
            render_plan.expected_quotient,
        );
        model.quotient_probe = render_plan.quotient_probe;
        model.render(&mut verifier_output).map_err(|_| GeneratorError::Render {
            artifact: "Halo2Verifier.sol",
        })?;
        Ok(verifier_output)
    }

    /// Render a test-only quotient probe: the verifier for `lowering` (with a
    /// separate VK contract) that returns `[expected_eval,
    /// selector_acc[0..n)]` right after the quotient section instead of
    /// verifying the proof. For differential tests of the emitted quotient
    /// Yul only; [`Self::render`] never produces it, and the probe is not a
    /// verifier.
    #[cfg(feature = "evm")]
    #[doc(hidden)]
    pub fn render_quotient_probe(
        &self,
        lowering: QuotientLowering,
    ) -> Result<crate::api::QuotientProbeArtifacts, GeneratorError> {
        let inputs = self.inputs();
        let plan = inputs.lowering_plan_for(lowering)?;
        let verifier = self.render_verifier_source_with_plan(
            &inputs,
            &plan,
            VerifierRenderPlan {
                separate: true,
                trace: false,
                gas_checkpoints: false,
                external_quotient: false,
                expected_quotient: None,
                quotient_probe: true,
            },
        )?;
        let verifying_key = Self::render_vk_model(&plan.vk)?;
        Ok(crate::api::QuotientProbeArtifacts {
            verifier,
            verifying_key,
            selector_columns: plan.sorted_simple.clone(),
        })
    }

    /// Render the separate verifying-key payload contract.
    fn render_vk_model(vk: &Halo2VerifyingKey) -> Result<String, GeneratorError> {
        let mut vk_output = String::new();
        vk.render(&mut vk_output).map_err(|_| GeneratorError::Render {
            artifact: "Halo2VerifyingKey.sol",
        })?;
        Ok(vk_output)
    }
}
