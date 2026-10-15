# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.constant_planes-a1.normalization-a1.frame_flip-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-9eac917eb7/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.constant_planes-a1.normalization-a1`
- Child key: `frame_flip`
- Declaration: `Submission.cbr_ci_cp_exists_orthonormal_frame_eval_neg`
- Exact Lean type: `∀ (P d : ℕ) (v : Fin (d + 1) → Euclid P), Orthonormal ℝ v → ∃ w : Fin (d + 1) → Euclid P, Orthonormal ℝ w ∧ Submodule.span ℝ (Set.range w) = Submodule.span ℝ (Set.range v) ∧ ∀ β : Covector (Euclid P) (d + 1), β w = -β v`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
