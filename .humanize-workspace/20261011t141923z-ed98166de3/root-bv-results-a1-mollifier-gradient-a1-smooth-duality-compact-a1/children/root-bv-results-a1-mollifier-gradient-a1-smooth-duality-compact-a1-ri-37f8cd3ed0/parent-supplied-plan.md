# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.bv_results-a1.mollifier_gradient-a1.smooth_duality_compact-a1.riesz_gradient-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-bv-results-a1-mollifier-gradient-a1-smooth-duality-compact-a1-ri-37f8cd3ed0/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.bv_results-a1.mollifier_gradient-a1.smooth_duality_compact-a1`
- Child key: `riesz_gradient`
- Declaration: `Submission.bv_exists_contDiff_gradient_of_contDiff_two`
- Exact Lean type: `∀ (n : ℕ) (w : Rn n → ℝ), ContDiff ℝ 2 w → ∃ G : Rn n → Rn n, ContDiff ℝ 1 G ∧ (∀ x v, inner ℝ (G x) v = fderiv ℝ w x v) ∧ ∀ x, ‖G x‖ = ‖fderiv ℝ w x‖`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
