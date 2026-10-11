# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.chart_tangent_differential-a1.chart_differential-a1.local_rademacher-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-chart-tangent-differential-a1-chart-differential-a1-local-rademacher-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.chart_tangent_differential-a1.chart_differential-a1`
- Child key: `local_rademacher`
- Declaration: `Submission.chartTD_ae_differentiableAt_of_locallyLipschitzOn`
- Exact Lean type: `∀ (n p : ℕ) (W : Set (Rn n)) (g : Rn n → Rn p), IsOpen W → LocallyLipschitzOn W g → ∀ᵐ u ∂(volume : Measure (Rn n)), u ∈ W → DifferentiableAt ℝ g u`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
