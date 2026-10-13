# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.de_giorgi-a1.density_estimates-a1.normal_average_bounds-a1.reduced_boundary_basic-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-de-giorgi-a1-density-estimates-a1-normal-average-bounds-a1-reduc-a87af9b396/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.de_giorgi-a1.density_estimates-a1.normal_average_bounds-a1`
- Child key: `reduced_boundary_basic`
- Declaration: `Submission.deGiorgiNAB_reducedBoundary_basic`
- Exact Lean type: `∀ (N : ℕ) (U : Set (Rn N)) (μ : Measure (Rn N)) (ν : Rn N → Rn N), ∀ x ∈ reducedBoundary U μ ν, x ∈ U ∧ ‖reducedNormal μ ν x‖ = 1 ∧ Tendsto (normalAverage μ ν x) (𝓝[>] 0) (𝓝 (reducedNormal μ ν x)) ∧ ∀ ρ : ℝ, 0 < ρ → 0 < μ (Metric.ball x ρ)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
