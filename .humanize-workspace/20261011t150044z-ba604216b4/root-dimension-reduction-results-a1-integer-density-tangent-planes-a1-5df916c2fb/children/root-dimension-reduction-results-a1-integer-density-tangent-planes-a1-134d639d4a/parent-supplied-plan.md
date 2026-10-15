# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.cone_splitting-a1.subspace_projection-a1.projection_invariance-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-134d639d4a/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.cone_splitting-a1.subspace_projection-a1`
- Child key: `projection_invariance`
- Declaration: `Submission.idtp_fons_cs_sp_action_starProjection_eq`
- Exact Lean type: `∀ (P m : ℕ) (R : IMRep (univ : Set (Euclid P)) m) (V : Submodule ℝ (Euclid P)), R.measure ((V : Set (Euclid P))ᶜ) = 0 → ∀ ω : DifferentialForm (Euclid P) m, R.action (affinePullbackForm V.starProjection 0 ω) = R.action ω`

## Sibling prerequisites

- `root.minimizing_implies_stationary-a1.approx_tangent_in_submanifold-a1.approx_tangent_le_flat-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
