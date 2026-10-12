# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.de_giorgi-a1.density_estimates-a1.ball_isoperimetric-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-de-giorgi-a1-density-estimates-a1-ball-isoperimetric-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.de_giorgi-a1.density_estimates-a1`
- Child key: `ball_isoperimetric`
- Declaration: `Submission.deGiorgiDens_ball_isoperimetric`
- Exact Lean type: `∀ (n : ℕ), ∃ c : ℝ, 0 < c ∧ ∀ (U G : Set (Rn (n + 1))) (μ : Measure (Rn (n + 1))) (ν : Rn (n + 1) → Rn (n + 1)), IsOpen U → NullMeasurableSet G volume → IsGaussGreenPair U G μ ν → ∀ (x : Rn (n + 1)) (ρ d : ℝ), 0 < ρ → Metric.closedBall x ρ ⊆ U → 0 < volume (G ∩ Metric.ball x ρ) → HasDerivAt (fun r : ℝ ↦ (volume (G ∩ Metric.ball x r)).toReal) d ρ → (volume (G ∩ Metric.ball x ρ)).toReal ^ ((n : ℝ) / (n + 1)) ≤ c * ((μ (Metric.ball x ρ)).toReal + d)`

## Sibling prerequisites

- `root.de_giorgi-a1.density_estimates-a1.radial_cutoff-a1`
- `root.de_giorgi-a1.density_estimates-a1.sobolev_indicator-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
