# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1.blowup_halfspace-a1.rescaled_gauss_green-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-2a232329dc/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1.blowup_halfspace-a1`
- Child key: `rescaled_gauss_green`
- Declaration: `Submission.codim1_rdo_dg_bh_rescaled_gauss_green`
- Exact Lean type: `∀ (m : ℕ) (D F : Set (Euclid (m + 1))) (μ : Measure (Euclid (m + 1))) (ν : Euclid (m + 1) → Euclid (m + 1)) (y : Euclid (m + 1)) (r R : ℝ), MeasurableSet F → (∀ φ : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ D → ∫ z in F, LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ φ z : Euclid (m + 1) →ₗ[ℝ] Euclid (m + 1)) = -∫ z, inner ℝ (φ z) (ν z) ∂μ) → 0 < r → closedBall y (r * R) ⊆ D → ∀ g : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ 1 g → HasCompactSupport g → tsupport g ⊆ ball (0 : Euclid (m + 1)) R → ∫ w in (fun w => y + r • w) ⁻¹' F, LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ g w : Euclid (m + 1) →ₗ[ℝ] Euclid (m + 1)) = -(r ^ m)⁻¹ * ∫ z, inner ℝ (g (r⁻¹ • (z - y))) (ν z) ∂μ`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
