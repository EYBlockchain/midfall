// SPDX-License-Identifier: CC0-1.0
//! Options-driven rendering entry points for `SolidityGenerator`.

use ruint::aliases::U256;

use super::*;
use crate::{
    api::{RenderQuotient, RenderVk},
    lowering::{
        plan::LoweringPlan, quotient_listing::QuotientListingContext, render::Halo2VerifyingKey,
    },
};

struct VerifierRenderPlan {
    separate: bool,
    trace: bool,
    gas_checkpoints: bool,
    external_quotient: bool,
    expected_quotient: Option<(usize, U256)>,
}

impl<'a> SolidityGenerator<'a> {
    /// Render generated Solidity artifacts according to one immutable options
    /// value.
    ///
    /// Besides the Solidity sources, the result carries the quotient-VM
    /// listing and identity manifest (`quotient_listing`,
    /// `quotient_manifest`). They are built after, and independently of, the
    /// Solidity sources from the same converged plan, and rendering fails if
    /// their translation validation against the Rust gate polynomials fails.
    pub fn render(&self, options: RenderOptions) -> Result<RenderedArtifacts, GeneratorError> {
        self.render_with_listing(options, true)
    }

    /// `render`, with the quotient listing/manifest optional (crate tests
    /// use `false` to show the Solidity does not depend on the listing).
    pub(crate) fn render_with_listing(
        &self,
        options: RenderOptions,
        emit_listing: bool,
    ) -> Result<RenderedArtifacts, GeneratorError> {
        let separate = matches!(options.vk, RenderVk::Separate);
        let (external_quotient, expected_quotient) = match options.quotient {
            RenderQuotient::Inline => (false, None),
            RenderQuotient::ExternalPinned {
                runtime_len,
                codehash,
            } => (true, Some((runtime_len, codehash))),
        };

        let inputs = self.inputs();
        let plan = inputs.lowering_plan();

        let render_plan = VerifierRenderPlan {
            separate,
            trace: options.diagnostics.trace,
            gas_checkpoints: options.diagnostics.gas_checkpoints,
            external_quotient,
            expected_quotient,
        };
        let verifier = self.render_verifier_source_with_plan(&inputs, &plan, render_plan)?;

        let verifying_key = separate.then(|| Self::render_vk_model(&plan.vk)).transpose()?;
        let quotient_evaluator = external_quotient
            .then(|| self.render_quotient_evaluator_with_plan(&inputs, &plan, options.diagnostics))
            .transpose()?;

        // The listing/manifest are read-only views of the same converged plan
        // and rendered VK payload; they are produced after every Solidity
        // artifact so they cannot influence it.
        let (quotient_listing, quotient_manifest) = if emit_listing {
            let artifacts = inputs
                .quotient_listing_artifacts(
                    &plan,
                    QuotientListingContext {
                        separate_vk: separate,
                        external_quotient,
                        trace: options.diagnostics.trace,
                    },
                )
                .map_err(|message| GeneratorError::Planning {
                    stage: "quotient listing",
                    message,
                })?;
            (Some(artifacts.listing), Some(artifacts.manifest))
        } else {
            (None, None)
        };

        Ok(RenderedArtifacts {
            verifier,
            verifying_key,
            quotient_evaluator,
            quotient_listing,
            quotient_manifest,
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
        inputs
            .generate_verifier_from_plan(
                plan,
                render_plan.separate,
                render_plan.trace,
                render_plan.gas_checkpoints,
                render_plan.external_quotient,
                render_plan.expected_quotient,
            )
            .render(&mut verifier_output)
            .map_err(|_| GeneratorError::Render {
                artifact: "Halo2Verifier.sol",
            })?;
        Ok(verifier_output)
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
