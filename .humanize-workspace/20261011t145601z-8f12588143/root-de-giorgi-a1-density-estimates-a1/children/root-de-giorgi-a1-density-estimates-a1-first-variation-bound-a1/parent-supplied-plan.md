# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.de_giorgi-a1.density_estimates-a1.first_variation_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-de-giorgi-a1-density-estimates-a1-first-variation-bound-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.de_giorgi-a1.density_estimates-a1`
- Child key: `first_variation_bound`
- Declaration: `Submission.deGiorgiDens_ball_normal_le_deriv`
- Exact Lean type: `∀ (N : ℕ) (U G : Set (Rn N)) (μ : Measure (Rn N)) (ν : Rn N → Rn N), IsOpen U → NullMeasurableSet G volume → IsGaussGreenPair U G μ ν → ∀ (x w : Rn N) (ρ d : ℝ), 0 < ρ → Metric.closedBall x ρ ⊆ U → ‖w‖ ≤ 1 → HasDerivAt (fun r : ℝ ↦ (volume (G ∩ Metric.ball x r)).toReal) d ρ → ∫ y in Metric.ball x ρ, inner ℝ (ν y) w ∂μ ≤ d`

## Sibling prerequisites

- `root.de_giorgi-a1.density_estimates-a1.lipschitz_gauss_green-a1`
- `root.de_giorgi-a1.density_estimates-a1.radial_cutoff-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
