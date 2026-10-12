# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.chart_tangent_differential-a1.lebesgue_points-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-chart-tangent-differential-a1-lebesgue-points-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.chart_tangent_differential-a1`
- Child key: `lebesgue_points`
- Declaration: `Submission.chartTD_lebesgue_point_ae`
- Exact Lean type: `∀ (n N : ℕ) (S : Set (Rn N)) (w : Rn N → ℝ) (C : ℝ), NullMeasurableSet S μHE[n] → μHE[n] S < ∞ → IntegrableOn w S μHE[n] → (∀ x ∈ S, ∀ ρ : ℝ, 0 < ρ → μHE[n] (S ∩ Metric.closedBall x ρ) ≤ ENNReal.ofReal (C * ρ ^ n)) → ∀ᵐ x ∂(μHE[n] : Measure (Rn N)), x ∈ S → Tendsto (fun ρ : ℝ ↦ (ρ ^ n)⁻¹ * ∫ z in S ∩ Metric.ball x ρ, |w z - w x| ∂μHE[n]) (𝓝[>] 0) (𝓝 0)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
