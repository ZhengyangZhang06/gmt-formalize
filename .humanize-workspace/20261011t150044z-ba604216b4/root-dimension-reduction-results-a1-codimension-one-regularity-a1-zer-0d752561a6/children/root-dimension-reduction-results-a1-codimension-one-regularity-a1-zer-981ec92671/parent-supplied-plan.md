# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.zero_scale_limit_plane-a1.graph_blowup_limit-a1.centre_offsets-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-zer-981ec92671/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.zero_scale_limit_plane-a1.graph_blowup_limit-a1`
- Child key: `centre_offsets`
- Declaration: `Submission.codim1_zsl_gbl_centre_chart_offsets`
- Exact Lean type: `∀ (m k P : ℕ) (N : Set (Euclid P)) (x : Euclid P) (xs : ℕ → Euclid P) (lams : ℕ → ℝ) (ι : Euclid m →ₗᵢ[ℝ] Euclid P) (ι' : Euclid k →ₗᵢ[ℝ] Euclid P) (u : Euclid m → Euclid k) (δ₁ δ₂ C₀ : ℝ), Tendsto xs atTop (𝓝 x) → Tendsto lams atTop (𝓝 0) → (∀ i, 0 < lams i) → (∀ i, ∃ p ∈ N, dist p (xs i) ≤ C₀ * lams i) → (∀ v w, inner ℝ (ι v) (ι' w) = 0) → (∀ y : Euclid P, ∃ v w, y = ι v + ι' w) → 0 < δ₁ → 0 < δ₂ → N ∩ {y | ∃ v ∈ ball (0 : Euclid m) δ₁, ∃ w ∈ ball (0 : Euclid k) δ₂, y = x + ι v + ι' w} = (fun v => x + ι v + ι' (u v)) '' ball (0 : Euclid m) δ₁ → ∃ (s : ℕ → Euclid m) (t : ℕ → Euclid k), (∀ i, xs i = x + ι (s i) + ι' (t i)) ∧ Tendsto s atTop (𝓝 0) ∧ Tendsto t atTop (𝓝 0) ∧ ∀ᶠ i in atTop, ∃ w : Euclid m, ‖w‖ ≤ C₀ ∧ s i + lams i • w ∈ ball (0 : Euclid m) δ₁ ∧ ‖u (s i + lams i • w) - t i‖ ≤ C₀ * lams i`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
