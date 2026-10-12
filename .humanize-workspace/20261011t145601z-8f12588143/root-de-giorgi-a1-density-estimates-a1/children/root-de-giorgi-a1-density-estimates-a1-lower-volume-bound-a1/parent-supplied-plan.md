# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.de_giorgi-a1.density_estimates-a1.lower_volume_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-de-giorgi-a1-density-estimates-a1-lower-volume-bound-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.de_giorgi-a1.density_estimates-a1`
- Child key: `lower_volume_bound`
- Declaration: `Submission.deGiorgiDens_ball_volume_ge`
- Exact Lean type: `∀ (n : ℕ), ∃ c : ℝ, 0 < c ∧ ∀ (U G : Set (Rn (n + 1))) (μ : Measure (Rn (n + 1))) (ν : Rn (n + 1) → Rn (n + 1)), IsOpen U → NullMeasurableSet G volume → IsGaussGreenPair U G μ ν → ∀ (x w : Rn (n + 1)) (ρ₁ : ℝ), ‖w‖ ≤ 1 → Metric.ball x ρ₁ ⊆ U → (∀ ρ ∈ Ioo 0 ρ₁, 0 < μ (Metric.ball x ρ) ∧ (μ (Metric.ball x ρ)).toReal ≤ 2 * ∫ y in Metric.ball x ρ, inner ℝ (ν y) w ∂μ) → ∀ ρ ∈ Ioo 0 ρ₁, ENNReal.ofReal (c * ρ ^ (n + 1)) ≤ volume (G ∩ Metric.ball x ρ)`

## Sibling prerequisites

- `root.de_giorgi-a1.density_estimates-a1.first_variation_bound-a1`
- `root.de_giorgi-a1.density_estimates-a1.ball_isoperimetric-a1`
- `root.de_giorgi-a1.density_estimates-a1.ode_lower_bound-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
