# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.variation_formulas-a1.gram_det_derivatives-a1.det_derivatives_at_one-a1.leibniz_derivative-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-variation-formulas-a1-gram-det-derivatives-a1-det-derivatives-at-b5996e7377/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.variation_formulas-a1.gram_det_derivatives-a1.det_derivatives_at_one-a1`
- Child key: `leibniz_derivative`
- Declaration: `Submission.variation_matrix_det_hasDerivAt_leibniz`
- Exact Lean type: `∀ (ι : Type) [Fintype ι] [DecidableEq ι] (G : ℝ → Matrix ι ι ℝ) (H : Matrix ι ι ℝ) (x : ℝ), (∀ i k, HasDerivAt (fun s ↦ G s i k) (H i k) x) → HasDerivAt (fun t ↦ (G t).det) (∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∑ m : ι, (∏ j ∈ Finset.univ.erase m, G x (σ j) j) * H (σ m) m) x`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
