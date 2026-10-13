# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.pointwise-a1.plane_unique-a1.span_le_of_det_eq-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-b1b707d1b3/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.pointwise-a1.plane_unique-a1`
- Child key: `span_le_of_det_eq`
- Declaration: `Submission.cbr_ci_pw_pu_span_le_of_inner_det_eq`
- Exact Lean type: `∀ (P n : ℕ) (x y : Fin n → Euclid P), Orthonormal ℝ x → Orthonormal ℝ y → (∀ w : Fin n → Euclid P, Matrix.det (Matrix.of fun a b => inner ℝ (x a) (w b)) = Matrix.det (Matrix.of fun a b => inner ℝ (y a) (w b))) → Submodule.span ℝ (Set.range y) ≤ Submodule.span ℝ (Set.range x)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
