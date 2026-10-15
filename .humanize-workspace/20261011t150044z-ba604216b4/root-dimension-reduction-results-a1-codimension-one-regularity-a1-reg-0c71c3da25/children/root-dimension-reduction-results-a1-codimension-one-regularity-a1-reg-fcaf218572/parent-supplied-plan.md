# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1.volume_density_lower-a1.finite_difference-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-fcaf218572/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1.volume_density_lower-a1`
- Child key: `finite_difference`
- Declaration: `Submission.codim1_rdo_dg_vdl_finite_difference`
- Exact Lean type: `∀ (m : ℕ) (D G : Set (Euclid (m + 1))) (μ : Measure (Euclid (m + 1))) (y : Euclid (m + 1)) (ρ₁ C₁ c : ℝ), 1 ≤ m → MeasurableSet G → 0 < c → 0 ≤ C₁ → closedBall y ρ₁ ⊆ D → μ (closedBall y ρ₁) ≠ ∞ → (∀ ζ : Euclid (m + 1) → ℝ, ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ D → (∀ z, 0 ≤ ζ z) → (∫ z in G, ζ z ^ ((m + 1 : ℝ) / m)) ^ ((m : ℝ) / (m + 1)) ≤ c * (∫ z, ζ z ∂μ + ∫ z in G, ‖fderiv ℝ ζ z‖)) → (∀ ρ δ : ℝ, 0 < ρ → 0 < δ → ρ + δ < ρ₁ → ENNReal.ofReal δ * μ (closedBall y ρ) ≤ ENNReal.ofReal C₁ * volume (G ∩ (ball y (ρ + δ) \ closedBall y ρ))) → ∃ K : ℝ, 0 < K ∧ ∀ ρ δ : ℝ, 0 < ρ → 0 < δ → ρ + δ < ρ₁ → (volume (G ∩ closedBall y ρ)).toReal ^ ((m : ℝ) / (m + 1)) ≤ K / δ * ((volume (G ∩ closedBall y (ρ + δ))).toReal - (volume (G ∩ closedBall y ρ)).toReal)`

## Sibling prerequisites

- `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1.volume_density_lower-a1.annular_cutoff-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
