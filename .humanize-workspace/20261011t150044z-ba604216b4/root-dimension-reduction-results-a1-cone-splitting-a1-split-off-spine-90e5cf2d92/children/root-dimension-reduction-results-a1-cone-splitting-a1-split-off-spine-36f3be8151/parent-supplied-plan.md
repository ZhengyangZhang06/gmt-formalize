# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.minimality_transfer-a1.cube_stokes-a1.translate_boundary-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-split-off-spine-36f3be8151/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.minimality_transfer-a1.cube_stokes-a1`
- Child key: `translate_boundary`
- Declaration: `Submission.dimred_cs_sos_mt_cs_translate_boundary_eval`
- Exact Lean type: `∀ (P m : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid P)) m) (Y : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)) (γ : DifferentialForm (Euclid P) m) (t : Euclid P), Y.boundary = X → IsTestForm γ → currentEval Y (fun y => exteriorDerivative γ (t + y)) = currentEval X (fun y => γ (t + y))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
