# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.chart_tangent_differential-a1.weighted_tangent_combination-a1.weighted_blowup_split-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-chart-tangent-differential-a1-weighted-tangent-combination-a1-we-e8a5369a83/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.chart_tangent_differential-a1.weighted_tangent_combination-a1`
- Child key: `weighted_blowup_split`
- Declaration: `Submission.chartTD_weighted_blowup_integral_split`
- Exact Lean type: `∀ (n N : ℕ) (M Γ : Set (Rn N)) (θ : Rn N → ℝ) (x : Rn N) (f : C_c(Rn N, ℝ)) (r : ℝ), 0 < r → NullMeasurableSet M μHE[n] → NullMeasurableSet Γ μHE[n] → μHE[n] Γ < ∞ → IsPositiveLocallyIntegrableWeight n M θ → ∫ z in M, f (blowUpMap x r z) * θ z ∂μHE[n] = ∫ z in M \ Γ, f (blowUpMap x r z) * θ z ∂μHE[n] + θ x * (∫ z in Γ, f (blowUpMap x r z) ∂μHE[n] - ∫ z in Γ \ M, f (blowUpMap x r z) ∂μHE[n]) + ∫ z in M ∩ Γ, f (blowUpMap x r z) * (θ z - θ x) ∂μHE[n]`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
