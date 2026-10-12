# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.chart_tangent_differential-a1.chart_image_measure-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-chart-tangent-differential-a1-chart-image-measure-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.chart_tangent_differential-a1`
- Child key: `chart_image_measure`
- Declaration: `Submission.chartTD_biLipschitz_image_measure_facts`
- Exact Lean type: `∀ (n N : ℕ) (B : Set (Rn n)) (ψ : Rn n → Rn N) (K : ℝ≥0) (c : ℝ), IsOpen B → Bornology.IsBounded B → LipschitzOnWith K ψ B → 0 < c → (∀ u ∈ B, ∀ u' ∈ B, c * ‖u - u'‖ ≤ ‖ψ u - ψ u'‖) → NullMeasurableSet (ψ '' B) μHE[n] ∧ Bornology.IsBounded (ψ '' B) ∧ μHE[n] (ψ '' B) < ∞ ∧ (∃ C : ℝ, ∀ x ∈ ψ '' B, ∀ ρ : ℝ, 0 < ρ → μHE[n] (ψ '' B ∩ Metric.closedBall x ρ) ≤ ENNReal.ofReal (C * ρ ^ n)) ∧ ∀ Z : Set (Rn N), μHE[n] Z = 0 → volume (B ∩ ψ ⁻¹' Z) = 0`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
