# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1.flat_tangent_density-a1.test_lower_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-16525e52e2/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1.flat_tangent_density-a1`
- Child key: `test_lower_bound`
- Declaration: `Submission.codim1_rdo_dg_ftd_test_lower_bound`
- Exact Lean type: `∀ (N m : ℕ) (μ : Measure (Euclid N)) (y : Euclid N) (f : Euclid N → ℝ) (A : Set (Euclid N)) (L L' : ℝ), Continuous f → (∀ w, 0 ≤ f w) → (∀ w, f w ≤ 1) → (∀ w, w ∉ A → f w = 0) → Tendsto (fun r : ℝ => (r ^ m)⁻¹ * ∫ z, f (r⁻¹ • (z - y)) ∂μ) (𝓝[>] 0) (𝓝 L) → L' < L → ∀ᶠ r in 𝓝[>] (0 : ℝ), ENNReal.ofReal (L' * r ^ m) ≤ μ {z | r⁻¹ • (z - y) ∈ A}`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
