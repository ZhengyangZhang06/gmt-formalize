# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.chart_tangent_differential-a1.chart_blowup_tangent-a1.blowup_integral_limit-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-chart-tangent-differential-a1-chart-blowup-tangent-a1-blowup-int-a9db9b5461/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.chart_tangent_differential-a1.chart_blowup_tangent-a1`
- Child key: `blowup_integral_limit`
- Declaration: `Submission.chartTD_chart_blowup_integral_tendsto`
- Exact Lean type: `∀ (n N : ℕ) (B : Set (Rn n)) (ψ : Rn n → Rn N) (K : ℝ≥0) (c : ℝ), IsOpen B → ContDiffOn ℝ 1 ψ B → LipschitzOnWith K ψ B → 0 < c → (∀ u ∈ B, ∀ u' ∈ B, c * ‖u - u'‖ ≤ ‖ψ u - ψ u'‖) → ∀ u ∈ B, ∀ f : C_c(Rn N, ℝ), Tendsto (fun r : ℝ ↦ (r ^ n)⁻¹ * ∫ v in B, f (blowUpMap (ψ u) r (ψ v)) * (fderiv ℝ ψ v).toLinearMap.normDet) (𝓝[>] 0) (𝓝 ((fderiv ℝ ψ u).toLinearMap.normDet * ∫ y, f (fderiv ℝ ψ u y)))`

## Sibling prerequisites

- `root.chart_tangent_differential-a1.chart_blowup_tangent-a1.fderiv_bounds-a1`
- `root.chart_tangent_differential-a1.chart_blowup_tangent-a1.normdet_le_opnorm_pow-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
