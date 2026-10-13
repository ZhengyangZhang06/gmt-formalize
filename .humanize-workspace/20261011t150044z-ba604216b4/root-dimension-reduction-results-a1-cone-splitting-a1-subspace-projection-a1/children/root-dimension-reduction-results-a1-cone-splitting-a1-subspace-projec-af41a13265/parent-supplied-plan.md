# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.cone_splitting-a1.subspace_projection-a1.orient_projection-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-subspace-projec-af41a13265/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.cone_splitting-a1.subspace_projection-a1`
- Child key: `orient_projection`
- Declaration: `Submission.dimred_cs_sp_orient_projection_le`
- Exact Lean type: `∀ (P m : ℕ) (V Q : Submodule ℝ (Euclid P)) (ξ : MultiVector P m) (α : Covector (Euclid P) m), IsUnitOrientationOf ξ Q → |ξ (α.compContinuousLinearMap V.starProjection)| ≤ covectorEuclideanNorm α`

## Sibling prerequisites

- `root.minimizing_implies_stationary-a1.covector_gram_bounds-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
