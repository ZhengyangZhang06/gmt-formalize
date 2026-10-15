# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1.blowup_halfspace-a1.normal_defect-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-50dd020301/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1.blowup_halfspace-a1`
- Child key: `normal_defect`
- Declaration: `Submission.codim1_rdo_dg_bh_normal_defect_small`
- Exact Lean type: `∀ (m : ℕ) (μ : Measure (Euclid (m + 1))) (ν : Euclid (m + 1) → Euclid (m + 1)) (y v : Euclid (m + 1)), Measurable ν → (∀ z, ‖ν z‖ = 1) → ‖v‖ = 1 → (∃ ρ₀ : ℝ, 0 < ρ₀ ∧ μ (closedBall y ρ₀) ≠ ∞) → Tendsto (fun ρ : ℝ => (μ (closedBall y ρ)).toReal⁻¹ • ∫ z in closedBall y ρ, ν z ∂μ) (𝓝[>] 0) (𝓝 v) → ∀ δ : ℝ, 0 < δ → ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ∫ z in closedBall y ρ, (1 - inner ℝ (ν z) v) ∂μ ≤ δ * (μ (closedBall y ρ)).toReal ∧ ∀ w : Euclid (m + 1), inner ℝ w v = 0 → ∫ z in closedBall y ρ, |inner ℝ (ν z) w| ∂μ ≤ δ * ‖w‖ * (μ (closedBall y ρ)).toReal`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
