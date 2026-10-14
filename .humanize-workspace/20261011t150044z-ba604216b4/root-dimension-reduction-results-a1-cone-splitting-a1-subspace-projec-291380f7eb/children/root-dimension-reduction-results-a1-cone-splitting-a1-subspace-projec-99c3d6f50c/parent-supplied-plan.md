# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.cone_splitting-a1.subspace_projection-a1.current_pushforward-a1.cycle_exact-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-subspace-projec-99c3d6f50c/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.cone_splitting-a1.subspace_projection-a1.current_pushforward-a1`
- Child key: `cycle_exact`
- Declaration: `Submission.dimred_cs_sp_cp_action_extDeriv_eq_zero`
- Exact Lean type: `∀ (P k : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid P)) (k + 1)) (R : IMRep (univ : Set (Euclid P)) (k + 1)) (K : Set (Euclid P)) (η : DifferentialForm (Euclid P) k), R.Represents X → IsCompact K → R.measure Kᶜ = 0 → X.boundary = 0 → IsSmoothForm η → R.action (exteriorDerivative η) = 0`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
