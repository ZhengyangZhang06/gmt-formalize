# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.variation_formulas-a1.gram_det_identity-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-variation-formulas-a1-gram-det-identity-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.variation_formulas-a1`
- Child key: `gram_det_identity`
- Declaration: `Submission.variation_gram_det_identity`
- Exact Lean type: `∀ (N N' : ℕ) (T : Submodule ℝ (Rn N)) (A : Rn N →L[ℝ] Rn N'), areaJacobian (A.comp T.subtypeL) = Real.sqrt ((1 - T.starProjection + T.starProjection ∘L ContinuousLinearMap.adjoint A ∘L A ∘L T.starProjection).det)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
