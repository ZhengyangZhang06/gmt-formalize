# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.rectifiable-a1.cone_density-a1.blowup_upper-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-bfaeb8601b/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.rectifiable-a1.cone_density-a1`
- Child key: `blowup_upper`
- Declaration: `Submission.cbrr_tcd_blowUp_preimage_le_of_testFunction`
- Exact Lean type: `∀ (P n : ℕ) (M : Set (Euclid P)) (x : Euclid P) (Q : Submodule ℝ (Euclid P)) (U : Set (Euclid P)) (f : CompactlySupportedContinuousMap (Euclid P) ℝ), μHE[n] M ≠ ∞ → HasApproximateTangentSpaceAt n M x Q → MeasurableSet U → (∀ y, 0 ≤ f y) → (∀ y ∈ U, 1 ≤ f y) → ∀ t : ℝ≥0∞, ENNReal.ofReal (∫ y in (Q : Set (Euclid P)), f y ∂μHE[n]) < t → ∀ᶠ r in 𝓝[>] (0 : ℝ), μHE[n] (M ∩ Poincare.SimonGMT.Chapter03.blowUpMap x r ⁻¹' U) ≤ t * ENNReal.ofReal (r ^ n)`

## Sibling prerequisites

- `root.regular_set_dense-a1.constant_multiplicity_reduction-a1.imrep_restrict-a1.blowup_image_measure-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
