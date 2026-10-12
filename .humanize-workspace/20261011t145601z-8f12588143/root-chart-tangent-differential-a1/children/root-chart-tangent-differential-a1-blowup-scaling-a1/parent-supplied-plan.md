# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.chart_tangent_differential-a1.blowup_scaling-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-chart-tangent-differential-a1-blowup-scaling-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.chart_tangent_differential-a1`
- Child key: `blowup_scaling`
- Declaration: `Submission.chartTD_setIntegral_blowUpMap_image`
- Exact Lean type: `∀ (N n : ℕ) (x : Rn N) (r : ℝ), 0 < r → ∀ (A : Set (Rn N)) (g : Rn N → ℝ), ∫ y in blowUpMap x r '' A, g y ∂μHE[n] = (r ^ n)⁻¹ * ∫ z in A, g (blowUpMap x r z) ∂μHE[n]`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
