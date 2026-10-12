# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.bv_results-a1.lipschitz_ibp-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-bv-results-a1-lipschitz-ibp-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.bv_results-a1`
- Child key: `lipschitz_ibp`
- Declaration: `Submission.bv_lipschitz_integration_by_parts`
- Exact Lean type: `∀ (n : ℕ) (F : Rn n → ℝ) (g : Rn n → Rn n) (K : ℝ≥0), ContDiff ℝ 1 F → LipschitzWith K g → HasCompactSupport g → ∫ x, F x * Chapter02.euclideanDivergence g x = -∫ x, fderiv ℝ F x (g x)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
