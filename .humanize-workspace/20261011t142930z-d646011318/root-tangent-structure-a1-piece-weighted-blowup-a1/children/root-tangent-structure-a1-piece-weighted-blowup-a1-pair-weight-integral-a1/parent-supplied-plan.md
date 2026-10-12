# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.tangent_structure-a1.piece_weighted_blowup-a1.pair_weight_integral-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-tangent-structure-a1-piece-weighted-blowup-a1-pair-weight-integral-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.tangent_structure-a1.piece_weighted_blowup-a1`
- Child key: `pair_weight_integral`
- Declaration: `Submission.ts_pwb_pair_weight_integral`
- Exact Lean type: `∀ (n ℓ : ℕ) (a : RectifiablePair n ℓ), IsFiniteMeasureOnCompacts (mk a).weight ∧ ∀ g : Ambient n ℓ → ℝ, ∫ y, g y ∂(mk a).weight = ∫ y in a.M, a.θ y * g y ∂μHE[n]`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
