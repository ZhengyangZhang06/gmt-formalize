# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.variation_formulas-a1.image_area_formula-a1.jacobian_chain_rule-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-variation-formulas-a1-image-area-formula-a1-jacobian-chain-rule-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.variation_formulas-a1.image_area_formula-a1`
- Child key: `jacobian_chain_rule`
- Declaration: `Submission.variation_areaJacobian_chain_rule`
- Exact Lean type: `∀ (n N N' : ℕ) (L : Rn n →L[ℝ] Rn N) (A : Rn N →L[ℝ] Rn N') (T : Submodule ℝ (Rn N)), T = LinearMap.range L.toLinearMap → areaJacobian (A.comp L) = areaJacobian (A.comp T.subtypeL) * areaJacobian L`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
