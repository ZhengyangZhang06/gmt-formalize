# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.bv_results-a1.mollifier_gradient-a1.div_conv-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-bv-results-a1-mollifier-gradient-a1-div-conv-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.bv_results-a1.mollifier_gradient-a1`
- Child key: `div_conv`
- Declaration: `Submission.bv_euclideanDivergence_convolution`
- Exact Lean type: `∀ (n : ℕ) (κ : Rn n → ℝ) (g : Rn n → Rn n), LocallyIntegrable κ volume → ContDiff ℝ 1 g → HasCompactSupport g → ∀ x, Chapter02.euclideanDivergence (convolution κ g (ContinuousLinearMap.lsmul ℝ ℝ) volume) x = convolution κ (Chapter02.euclideanDivergence g) (ContinuousLinearMap.lsmul ℝ ℝ) volume x`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
