# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.cone_splitting-a1.product_support_density-a1.ball_formula-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-product-support-75bcfccec1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.cone_splitting-a1.product_support_density-a1`
- Child key: `ball_formula`
- Declaration: `Submission.dimred_cs_psd_ball_formula`
- Exact Lean type: `∀ (P : ℕ) (L : Submodule ℝ (Euclid P)) (μ μ₀ : Measure (Euclid P)), μ₀ (Lᗮ : Set (Euclid P))ᶜ = 0 → (∀ A : Set (Euclid P), MeasurableSet A → μ A = ∫⁻ t in (L : Set (Euclid P)), μ₀ ((fun y => t + y) ⁻¹' A) ∂μHE[Module.finrank ℝ L]) → ∀ t ∈ L, ∀ y ∈ Lᗮ, ∀ ρ : ℝ, 0 < ρ → μ (ball (t + y) ρ) = ∫⁻ σ : Euclid (Module.finrank ℝ L), μ₀ (ball y (Real.sqrt (ρ ^ 2 - ‖σ‖ ^ 2)))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
