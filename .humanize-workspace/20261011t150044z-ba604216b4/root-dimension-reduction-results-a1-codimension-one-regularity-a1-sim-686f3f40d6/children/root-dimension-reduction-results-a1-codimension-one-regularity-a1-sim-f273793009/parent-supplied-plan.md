# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.area_comparison-a1.piece_pushforward-a1.signed_area_transfer-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-sim-f273793009/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.area_comparison-a1.piece_pushforward-a1`
- Child key: `signed_area_transfer`
- Declaration: `Submission.codim1_ac_pp_setIntegral_transfer`
- Exact Lean type: `∀ (α β : Type) [MeasurableSpace α] [MeasurableSpace β] (μ : Measure α) (ν : Measure β) (Φ : α → β) (A : Set α) (B : Set β) (J : α → ℝ) (f : β → ℝ), (∀ x, 0 ≤ J x) → (∀ g : β → ℝ≥0∞, ∫⁻ y in B, g y ∂ν = ∫⁻ x in A, ENNReal.ofReal (J x) * g (Φ x) ∂μ) → Integrable f (ν.restrict B) → AEStronglyMeasurable (fun x => J x * f (Φ x)) (μ.restrict A) → Integrable (fun x => J x * f (Φ x)) (μ.restrict A) ∧ ∫ y in B, f y ∂ν = ∫ x in A, J x * f (Φ x) ∂μ`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
