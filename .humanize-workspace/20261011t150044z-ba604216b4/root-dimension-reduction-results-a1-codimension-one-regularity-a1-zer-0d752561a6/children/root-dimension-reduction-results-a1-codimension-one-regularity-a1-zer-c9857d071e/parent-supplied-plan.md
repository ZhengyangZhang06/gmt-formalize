# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.zero_scale_limit_plane-a1.graph_blowup_limit-a1.graph_flattening-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-zer-c9857d071e/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.zero_scale_limit_plane-a1.graph_blowup_limit-a1`
- Child key: `graph_flattening`
- Declaration: `Submission.codim1_zsl_gbl_rescaled_graph_flattening`
- Exact Lean type: `∀ (m k : ℕ) (u : Euclid m → Euclid k) (δ C₀ : ℝ) (s : ℕ → Euclid m) (t : ℕ → Euclid k) (lams : ℕ → ℝ), 0 < δ → ContDiffOn ℝ 1 u (ball 0 δ) → fderiv ℝ u 0 = 0 → (∀ i, 0 < lams i) → Tendsto s atTop (𝓝 0) → Tendsto lams atTop (𝓝 0) → (∀ᶠ i in atTop, ∃ w : Euclid m, ‖w‖ ≤ C₀ ∧ s i + lams i • w ∈ ball (0 : Euclid m) δ ∧ ‖u (s i + lams i • w) - t i‖ ≤ C₀ * lams i) → ∃ (σ : ℕ → ℕ) (b : Euclid k), StrictMono σ ∧ (∀ R : ℝ, 0 < R → ∀ᶠ i in atTop, ∀ w ∈ ball (0 : Euclid m) R, DifferentiableAt ℝ (fun w => (lams (σ i))⁻¹ • (u (s (σ i) + lams (σ i) • w) - t (σ i))) w) ∧ ∀ R ε : ℝ, 0 < R → 0 < ε → ∀ᶠ i in atTop, ∀ w ∈ ball (0 : Euclid m) R, ‖(lams (σ i))⁻¹ • (u (s (σ i) + lams (σ i) • w) - t (σ i)) - b‖ < ε ∧ ‖fderiv ℝ (fun w => (lams (σ i))⁻¹ • (u (s (σ i) + lams (σ i) • w) - t (σ i))) w‖ < ε`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
