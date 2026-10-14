# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.smooth_regularity-a1.difference_quotient-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-sim-507e38a5f4/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.smooth_regularity-a1`
- Child key: `difference_quotient`
- Declaration: `Submission.codim1_hcp_sr_difference_quotient`
- Exact Lean type: `∀ (m k : ℕ) (α : ℝ), 1 ≤ m → 0 < α → ∀ (f : Euclid m → (Euclid m →L[ℝ] Euclid k)) (x₀ : Euclid m) (R h₀ C : ℝ), 0 < R → 0 < h₀ → ContinuousOn f (ball x₀ R) → (∀ v : Euclid m, ‖v‖ = 1 → ∀ t : ℝ, t ≠ 0 → |t| < h₀ → (∀ x ∈ ball x₀ R, ‖t⁻¹ • (f (x + t • v) - f x)‖ ≤ C) ∧ ∀ x ∈ ball x₀ R, ∀ y ∈ ball x₀ R, ‖t⁻¹ • (f (x + t • v) - f x) - t⁻¹ • (f (y + t • v) - f y)‖ ≤ C * ‖x - y‖ ^ α) → ContDiffOn ℝ 1 f (ball x₀ R) ∧ (∀ x ∈ ball x₀ R, ‖fderiv ℝ f x‖ ≤ C) ∧ ∀ x ∈ ball x₀ R, ∀ y ∈ ball x₀ R, ‖fderiv ℝ f x - fderiv ℝ f y‖ ≤ C * ‖x - y‖ ^ α`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
