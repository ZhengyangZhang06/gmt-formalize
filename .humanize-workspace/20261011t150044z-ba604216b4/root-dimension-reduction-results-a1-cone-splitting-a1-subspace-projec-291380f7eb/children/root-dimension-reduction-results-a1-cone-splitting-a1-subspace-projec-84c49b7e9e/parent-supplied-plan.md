# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.cone_splitting-a1.subspace_projection-a1.current_pushforward-a1.support_closed-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-subspace-projec-84c49b7e9e/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.cone_splitting-a1.subspace_projection-a1.current_pushforward-a1`
- Child key: `support_closed`
- Declaration: `Submission.dimred_cs_sp_cp_support_subset_of_carrier_subset`
- Exact Lean type: `∀ (P n : ℕ) (Y : GeometricCurrentOn (univ : Set (Euclid P)) n) (R : IMRep (univ : Set (Euclid P)) n) (F : Set (Euclid P)), R.Represents Y → IsClosed F → R.carrier ⊆ F → Y.support ⊆ F`

## Sibling prerequisites

- `root.density_one_implies_regular-a1.imrep_mass_and_support-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
