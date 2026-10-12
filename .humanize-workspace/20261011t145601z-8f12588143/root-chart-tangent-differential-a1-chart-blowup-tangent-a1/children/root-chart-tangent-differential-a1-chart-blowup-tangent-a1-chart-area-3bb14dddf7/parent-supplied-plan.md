# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.chart_tangent_differential-a1.chart_blowup_tangent-a1.chart_area_integral-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-chart-tangent-differential-a1-chart-blowup-tangent-a1-chart-area-3bb14dddf7/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.chart_tangent_differential-a1.chart_blowup_tangent-a1`
- Child key: `chart_area_integral`
- Declaration: `Submission.chartTD_injective_area_setIntegral`
- Exact Lean type: `∀ (n N : ℕ) (B : Set (Rn n)) (ψ : Rn n → Rn N) (K : ℝ≥0), IsOpen B → LipschitzOnWith K ψ B → InjOn ψ B → ∀ g : Rn N → ℝ, Continuous g → ∫ y in ψ '' B, g y ∂μHE[n] = ∫ v in B, g (ψ v) * (fderiv ℝ ψ v).toLinearMap.normDet`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
