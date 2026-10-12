# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.chart_tangent_differential-a1.weighted_tangent_combination-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-chart-tangent-differential-a1-weighted-tangent-combination-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.chart_tangent_differential-a1`
- Child key: `weighted_tangent_combination`
- Declaration: `Submission.chartTD_weighted_tangent_of_density`
- Exact Lean type: `∀ (n N : ℕ) (M Γ : Set (Rn N)) (θ : Rn N → ℝ) (x : Rn N) (P : Submodule ℝ (Rn N)), NullMeasurableSet M μHE[n] → NullMeasurableSet Γ μHE[n] → μHE[n] Γ < ∞ → IsPositiveLocallyIntegrableWeight n M θ → HasApproximateTangentSpaceAt n Γ x P → Tendsto (fun ρ : ℝ ↦ (ρ ^ n)⁻¹ * ∫ z in (M \ Γ) ∩ Metric.ball x ρ, |θ z| ∂μHE[n]) (𝓝[>] 0) (𝓝 0) → Tendsto (fun ρ : ℝ ↦ (ρ ^ n)⁻¹ * (μHE[n] ((Γ \ M) ∩ Metric.ball x ρ)).toReal) (𝓝[>] 0) (𝓝 0) → Tendsto (fun ρ : ℝ ↦ (ρ ^ n)⁻¹ * ∫ z in M ∩ Γ ∩ Metric.ball x ρ, |θ z - θ x| ∂μHE[n]) (𝓝[>] 0) (𝓝 0) → HasWeightedApproximateTangentSpaceAt n M θ x P`

## Sibling prerequisites

- `root.chart_tangent_differential-a1.blowup_scaling-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
