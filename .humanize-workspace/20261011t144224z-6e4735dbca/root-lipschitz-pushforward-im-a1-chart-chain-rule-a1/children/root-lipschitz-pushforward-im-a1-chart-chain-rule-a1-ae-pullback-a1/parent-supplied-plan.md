# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.lipschitz_pushforward_im-a1.chart_chain_rule-a1.ae_pullback-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-chart-chain-rule-a1-ae-pullback-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.lipschitz_pushforward_im-a1.chart_chain_rule-a1`
- Child key: `ae_pullback`
- Declaration: `Submission.lpf_ccr_ae_pullback`
- Exact Lean type: `∀ (P n : ℕ) (M : Set (Eucl P)) (Φ : Eucl n → Eucl P) (Ω : Set (Eucl n)) (p : Eucl P → Prop), MeasurableSet Ω → Measurable Φ → (∃ c : ℝ, 0 < c ∧ ∀ w ∈ Ω, ∀ w' ∈ Ω, c * ‖w - w'‖ ≤ ‖Φ w - Φ w'‖) → NullMeasurableSet M (μHE[n] : Measure (Eucl P)) → (∀ᵐ x ∂((μHE[n] : Measure (Eucl P)).restrict (M ∩ Φ '' Ω)), p x) → NullMeasurableSet (Ω ∩ Φ ⁻¹' M) (volume : Measure (Eucl n)) ∧ ∀ᵐ w ∂((volume : Measure (Eucl n)).restrict (Ω ∩ Φ ⁻¹' M)), p (Φ w)`

## Sibling prerequisites

- `root.lipschitz_pushforward_im-a1.rectifiable_area_formula-a1.chart_preimage_null-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
