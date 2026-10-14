# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.lipschitz_pushforward_im-a1.chart_chain_rule-a1.ae_diff_comp-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-chart-chain-rule-a1-ae-diff-comp-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.lipschitz_pushforward_im-a1.chart_chain_rule-a1`
- Child key: `ae_diff_comp`
- Declaration: `Submission.lpf_ccr_ae_differentiableAt_comp`
- Exact Lean type: `∀ (P Q n : ℕ) (U : Set (Eucl P)) (f : Eucl P → Eucl Q) (Φ : Eucl n → Eucl P), IsOpen U → LocallyLipschitzOn U f → ContDiff ℝ 1 Φ → ∀ᵐ w ∂(volume : Measure (Eucl n)), Φ w ∈ U → DifferentiableAt ℝ (f ∘ Φ) w`

## Sibling prerequisites

- `root.lipschitz_pushforward_im-a1.locally_lipschitz_image-a1.countable_lipschitz_cover-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
