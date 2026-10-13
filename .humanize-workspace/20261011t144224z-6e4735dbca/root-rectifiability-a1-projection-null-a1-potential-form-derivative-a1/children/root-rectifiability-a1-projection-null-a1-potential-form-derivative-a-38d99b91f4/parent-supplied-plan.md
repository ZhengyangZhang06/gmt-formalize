# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.rectifiability-a1.projection_null-a1.potential_form_derivative-a1.wedge_cons_sign-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-rectifiability-a1-projection-null-a1-potential-form-derivative-a-38d99b91f4/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.rectifiability-a1.projection_null-a1.potential_form_derivative-a1`
- Child key: `wedge_cons_sign`
- Declaration: `Submission.rpn_pfd_wedge_cons_succAbove_sign`
- Exact Lean type: `∀ (P m : ℕ) (l : Fin (m + 1) → (Eucl P →L[ℝ] ℝ)) (j : Fin (m + 1)), wedgeCovectors (m + 1) (Fin.cons (l j) (fun k => l (j.succAbove k)) : Fin (m + 1) → (Eucl P →L[ℝ] ℝ)) = ((-1 : ℝ) ^ (j : ℕ)) • wedgeCovectors (m + 1) l ∧ ∀ i : Fin (m + 1), i ≠ j → wedgeCovectors (m + 1) (Fin.cons (l i) (fun k => l (j.succAbove k)) : Fin (m + 1) → (Eucl P →L[ℝ] ℝ)) = 0`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
