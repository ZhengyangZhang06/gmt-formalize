# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.rectifiability-a1.projection_null-a1.potential_form_derivative-a1.divergence_term-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-rectifiability-a1-projection-null-a1-potential-form-derivative-a-aaad8721ed/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.rectifiability-a1.projection_null-a1.potential_form_derivative-a1`
- Child key: `divergence_term`
- Declaration: `Submission.rpn_pfd_wedge_cons_comp_succAbove`
- Exact Lean type: `∀ (P m : ℕ) (L : Eucl P →L[ℝ] Eucl (m + 1)) (ℓ : Eucl (m + 1) →L[ℝ] ℝ) (j : Fin (m + 1)), wedgeCovectors (m + 1) (Fin.cons (ℓ.comp L) (fun i => (EuclideanSpace.proj (j.succAbove i) : Eucl (m + 1) →L[ℝ] ℝ).comp L) : Fin (m + 1) → (Eucl P →L[ℝ] ℝ)) = ((-1 : ℝ) ^ (j : ℕ) * ℓ (EuclideanSpace.single j (1 : ℝ))) • wedgeCovectors (m + 1) (fun i => (EuclideanSpace.proj i : Eucl (m + 1) →L[ℝ] ℝ).comp L)`

## Sibling prerequisites

- `root.rectifiability-a1.projection_null-a1.potential_form_derivative-a1.wedge_cons_linear-a1`
- `root.rectifiability-a1.projection_null-a1.potential_form_derivative-a1.wedge_cons_sign-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
