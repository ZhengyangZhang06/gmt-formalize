# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.zero_scale_limit_plane-a1.graph_blowup_limit-a1.mass_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-zer-fffedff989/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.zero_scale_limit_plane-a1.graph_blowup_limit-a1`
- Child key: `mass_bound`
- Declaration: `Submission.codim1_zsl_gbl_blowUp_mass_bound`
- Exact Lean type: `∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (x : Euclid P) (xs : ℕ → Euclid P) (lams : ℕ → ℝ) (hlams : ∀ i, 0 < lams i), Tendsto xs atTop (𝓝 x) → Tendsto lams atTop (𝓝 0) → (∃ C r₀ : ℝ, 0 < r₀ ∧ ∀ y ∈ ball x r₀, ∀ ρ : ℝ, 0 < ρ → ρ < r₀ → T.massOn (ball y ρ) ≤ ENNReal.ofReal (C * ρ ^ n)) → ∀ R : ℝ, 0 < R → ∃ c : ℝ, ∀ᶠ i in atTop, ∀ ω : TestFormOn (univ : Set (Euclid P)) n, tsupport (ω : DifferentialForm (Euclid P) n) ⊆ ball 0 R → (∀ y, covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) n) y) ≤ 1) → currentEval (blowUp T (xs i) (lams i) (hlams i).ne') (ω : DifferentialForm (Euclid P) n) ≤ c`

## Sibling prerequisites

- `root.density_and_tangent_cones-a1.blowup_scaling-a1.testform_correspondence-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
