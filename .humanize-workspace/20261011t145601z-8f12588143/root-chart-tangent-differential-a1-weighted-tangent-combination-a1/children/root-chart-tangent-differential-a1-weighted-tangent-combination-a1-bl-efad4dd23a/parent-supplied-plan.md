# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.chart_tangent_differential-a1.weighted_tangent_combination-a1.blowup_error_vanishes-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-chart-tangent-differential-a1-weighted-tangent-combination-a1-bl-efad4dd23a/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.chart_tangent_differential-a1.weighted_tangent_combination-a1`
- Child key: `blowup_error_vanishes`
- Declaration: `Submission.chartTD_blowup_integral_tendsto_zero`
- Exact Lean type: `∀ (n N : ℕ) (S : Set (Rn N)) (w : Rn N → ℝ) (x : Rn N), (∀ ρ : ℝ, 0 < ρ → IntegrableOn w (S ∩ Metric.ball x ρ) μHE[n]) → Tendsto (fun ρ : ℝ ↦ (ρ ^ n)⁻¹ * ∫ z in S ∩ Metric.ball x ρ, |w z| ∂μHE[n]) (𝓝[>] 0) (𝓝 0) → ∀ f : C_c(Rn N, ℝ), Tendsto (fun r : ℝ ↦ (r ^ n)⁻¹ * ∫ z in S, f (blowUpMap x r z) * w z ∂μHE[n]) (𝓝[>] 0) (𝓝 0)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
