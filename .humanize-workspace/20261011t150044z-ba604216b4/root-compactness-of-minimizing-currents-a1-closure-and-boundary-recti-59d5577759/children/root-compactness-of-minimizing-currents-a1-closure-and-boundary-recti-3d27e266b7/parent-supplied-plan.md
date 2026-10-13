# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.weight_ge_one-a1.interior_form-a1.covector_norm-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-3d27e266b7/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.weight_ge_one-a1.interior_form-a1`
- Child key: `covector_norm`
- Declaration: `Submission.cbr_ci_pw_ipf_covector_norm_eq`
- Exact Lean type: `∀ (d : ℕ) (z : Euclid (d + 1)) (ε : Covector (Euclid (d + 1)) d), (∀ i : Fin (d + 1), ε (i.removeNth (fun l : Fin (d + 1) => EuclideanSpace.single l (1 : ℝ))) = (-1 : ℝ) ^ (i : ℕ) * z i) → covectorEuclideanNorm ε = ‖z‖`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
