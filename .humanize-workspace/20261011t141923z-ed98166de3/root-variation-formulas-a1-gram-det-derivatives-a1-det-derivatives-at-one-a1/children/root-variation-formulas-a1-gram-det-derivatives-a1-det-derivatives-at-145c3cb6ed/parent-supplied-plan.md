# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.variation_formulas-a1.gram_det_derivatives-a1.det_derivatives_at_one-a1.first_order_at_one-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-variation-formulas-a1-gram-det-derivatives-a1-det-derivatives-at-145c3cb6ed/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.variation_formulas-a1.gram_det_derivatives-a1.det_derivatives_at_one-a1`
- Child key: `first_order_at_one`
- Declaration: `Submission.variation_matrix_det_leibniz_first_order_at_one`
- Exact Lean type: `∀ (ι : Type) [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℝ), ∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∑ m : ι, (∏ j ∈ Finset.univ.erase m, (1 : Matrix ι ι ℝ) (σ j) j) * H (σ m) m = H.trace`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
