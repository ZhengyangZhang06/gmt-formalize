# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.chart_tangent_differential-a1.local_bilipschitz-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-chart-tangent-differential-a1-local-bilipschitz-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.chart_tangent_differential-a1`
- Child key: `local_bilipschitz`
- Declaration: `Submission.chartTD_immersion_local_biLipschitz`
- Exact Lean type: `∀ (n N : ℕ) (V : Set (Rn n)) (ψ : Rn n → Rn N), IsOpen V → ContDiffOn ℝ 1 ψ V → (∀ u ∈ V, Function.Injective (fderiv ℝ ψ u)) → ∀ u₀ ∈ V, ∃ r : ℝ, 0 < r ∧ Metric.ball u₀ r ⊆ V ∧ ∃ (K : ℝ≥0) (c : ℝ), 0 < c ∧ LipschitzOnWith K ψ (Metric.ball u₀ r) ∧ ∀ u ∈ Metric.ball u₀ r, ∀ u' ∈ Metric.ball u₀ r, c * ‖u - u'‖ ≤ ‖ψ u - ψ u'‖`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
