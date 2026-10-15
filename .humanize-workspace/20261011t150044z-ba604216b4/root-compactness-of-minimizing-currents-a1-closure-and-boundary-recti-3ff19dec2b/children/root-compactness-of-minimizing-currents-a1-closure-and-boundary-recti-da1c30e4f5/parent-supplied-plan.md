# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.constant_planes-a1.projection_reduction-a1.det_expansion-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-da1c30e4f5/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.constant_planes-a1.projection_reduction-a1`
- Child key: `det_expansion`
- Declaration: `Submission.cbr_ci_cp_pr_factorial_mul_eq_sum_det`
- Exact Lean type: `∀ (P n : ℕ) (e : OrthonormalBasis (Fin P) ℝ (Euclid P)) (β : Covector (Euclid P) n) (u : Fin n → Euclid P), (n.factorial : ℝ) * β u = ∑ I : Fin n → Fin P, β (fun a => e (I a)) * Matrix.det (Matrix.of fun a b => inner ℝ (e (I b)) (u a))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
