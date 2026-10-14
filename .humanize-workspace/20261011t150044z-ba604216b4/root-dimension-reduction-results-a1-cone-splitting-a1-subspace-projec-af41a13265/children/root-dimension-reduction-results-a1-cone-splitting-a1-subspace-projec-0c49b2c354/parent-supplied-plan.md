# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.cone_splitting-a1.subspace_projection-a1.orient_projection-a1.projected_gram_det-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-subspace-projec-0c49b2c354/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.cone_splitting-a1.subspace_projection-a1.orient_projection-a1`
- Child key: `projected_gram_det`
- Declaration: `Submission.dimred_cs_sp_op_gram_det_starProjection_le_one`
- Exact Lean type: `∀ (P m : ℕ) (V : Submodule ℝ (Euclid P)) (τ : Fin m → Euclid P), Orthonormal ℝ τ → Matrix.det (Matrix.of fun i j => inner ℝ (V.starProjection (τ i)) (V.starProjection (τ j))) ≤ 1`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
