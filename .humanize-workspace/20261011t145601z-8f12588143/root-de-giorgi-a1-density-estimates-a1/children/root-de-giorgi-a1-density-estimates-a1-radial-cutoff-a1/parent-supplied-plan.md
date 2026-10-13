# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.de_giorgi-a1.density_estimates-a1.radial_cutoff-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-de-giorgi-a1-density-estimates-a1-radial-cutoff-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.de_giorgi-a1.density_estimates-a1`
- Child key: `radial_cutoff`
- Declaration: `Submission.deGiorgiDens_radial_cutoff`
- Exact Lean type: `∀ (N : ℕ) (x : Rn N) (s ρ : ℝ), 0 < s → s < ρ → ∃ ζ : Rn N → ℝ, (∃ K : ℝ≥0, LipschitzWith K ζ) ∧ HasCompactSupport ζ ∧ tsupport ζ ⊆ Metric.closedBall x ρ ∧ (∀ y, 0 ≤ ζ y ∧ ζ y ≤ 1) ∧ (∀ y ∈ Metric.ball x s, ζ y = 1) ∧ (∀ y ∉ Metric.ball x ρ, ζ y = 0) ∧ ∀ G : Set (Rn N), NullMeasurableSet G volume → ∫ y in G, ‖fderiv ℝ ζ y‖ = ((volume (G ∩ Metric.ball x ρ)).toReal - (volume (G ∩ Metric.ball x s)).toReal) / (ρ - s)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
