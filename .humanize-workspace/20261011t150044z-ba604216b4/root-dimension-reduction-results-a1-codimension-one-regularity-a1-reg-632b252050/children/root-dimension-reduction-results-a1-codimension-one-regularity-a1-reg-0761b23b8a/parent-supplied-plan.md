# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1.blowup_halfspace-a1.normal_limsup-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-0761b23b8a/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1.blowup_halfspace-a1`
- Child key: `normal_limsup`
- Declaration: `Submission.codim1_rdo_dg_bh_normal_limsup`
- Exact Lean type: `∀ (m : ℕ) (D F : Set (Euclid (m + 1))) (μ : Measure (Euclid (m + 1))) (ν : Euclid (m + 1) → Euclid (m + 1)) (y v : Euclid (m + 1)) (ρ₁ C₁ : ℝ), MeasurableSet F → Measurable ν → (∀ z, ‖ν z‖ = 1) → (∀ φ : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ D → ∫ z in F, LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ φ z : Euclid (m + 1) →ₗ[ℝ] Euclid (m + 1)) = -∫ z, inner ℝ (φ z) (ν z) ∂μ) → ‖v‖ = 1 → Tendsto (fun ρ : ℝ => (μ (closedBall y ρ)).toReal⁻¹ • ∫ z in closedBall y ρ, ν z ∂μ) (𝓝[>] 0) (𝓝 v) → 0 < ρ₁ → 0 ≤ C₁ → closedBall y ρ₁ ⊆ D → (∀ ρ : ℝ, 0 < ρ → ρ < ρ₁ → μ (closedBall y ρ) ≤ ENNReal.ofReal (C₁ * ρ ^ m)) → ∀ ζ : Euclid (m + 1) → ℝ, ContDiff ℝ 1 ζ → HasCompactSupport ζ → (∀ z, 0 ≤ ζ z) → ∀ δ : ℝ, 0 < δ → ∀ᶠ r in 𝓝[>] (0 : ℝ), ∫ z in (fun z => y + r • z) ⁻¹' F, fderiv ℝ ζ z v ≤ δ`

## Sibling prerequisites

- `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1.blowup_halfspace-a1.directional_gauss_green-a1`
- `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1.blowup_halfspace-a1.normal_defect-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
