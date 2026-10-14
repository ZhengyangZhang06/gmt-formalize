# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.constant_planes-a1.projection_reduction-a1.column_expansion-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-cee464319c/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.constant_planes-a1.projection_reduction-a1`
- Child key: `column_expansion`
- Declaration: `Submission.cbr_ci_cp_pr_det_covector_laplace`
- Exact Lean type: `∀ (P d : ℕ) (g : Fin (d + 1) → Euclid P) (k : Fin (d + 1)) (γ : Covector (Euclid P) (d + 1)), (∀ u : Fin (d + 1) → Euclid P, γ u = Matrix.det (Matrix.of fun a b => inner ℝ (g b) (u a))) → ∃ α : Covector (Euclid P) d, ∀ u : Fin (d + 1) → Euclid P, γ u = ∑ i : Fin (d + 1), (-1 : ℝ) ^ (i : ℕ) * (inner ℝ (g k) (u i) * α (i.removeNth u))`

## Sibling prerequisites

- `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.constant_planes-a1.projection_reduction-a1.det_covector-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
