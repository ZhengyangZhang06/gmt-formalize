# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1.volume_density_lower-a1.one_sided_density-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-113592b222/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1.volume_density_lower-a1`
- Child key: `one_sided_density`
- Declaration: `Submission.codim1_rdo_dg_vdl_one_sided_density`
- Exact Lean type: `∀ (m : ℕ) (D G : Set (Euclid (m + 1))) (μ : Measure (Euclid (m + 1))) (y : Euclid (m + 1)) (ρ₁ C₁ c : ℝ), 1 ≤ m → MeasurableSet G → 0 < c → 0 ≤ C₁ → closedBall y ρ₁ ⊆ D → μ (closedBall y ρ₁) ≠ ∞ → (∀ r : ℝ, 0 < r → μ (closedBall y r) ≠ 0) → (∀ ζ : Euclid (m + 1) → ℝ, ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ D → (∀ z, 0 ≤ ζ z) → (∫ z in G, ζ z ^ ((m + 1 : ℝ) / m)) ^ ((m : ℝ) / (m + 1)) ≤ c * (∫ z, ζ z ∂μ + ∫ z in G, ‖fderiv ℝ ζ z‖)) → (∀ ρ δ : ℝ, 0 < ρ → 0 < δ → ρ + δ < ρ₁ → ENNReal.ofReal δ * μ (closedBall y ρ) ≤ ENNReal.ofReal C₁ * volume (G ∩ (ball y (ρ + δ) \ closedBall y ρ))) → ∃ c' : ℝ, 0 < c' ∧ ∀ ρ : ℝ, 0 < ρ → ρ < ρ₁ → ENNReal.ofReal (c' * ρ ^ (m + 1)) ≤ volume (G ∩ ball y ρ)`

## Sibling prerequisites

- `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1.volume_density_lower-a1.discrete_growth-a1`
- `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1.volume_density_lower-a1.finite_difference-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
