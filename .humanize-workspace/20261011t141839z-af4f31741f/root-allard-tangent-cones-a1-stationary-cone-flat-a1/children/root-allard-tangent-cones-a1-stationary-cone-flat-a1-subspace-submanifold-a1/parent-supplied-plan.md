# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.allard_tangent_cones-a1.stationary_cone_flat-a1.subspace_submanifold-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-allard-tangent-cones-a1-stationary-cone-flat-a1-subspace-submanifold-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.allard_tangent_cones-a1.stationary_cone_flat-a1`
- Child key: `subspace_submanifold`
- Declaration: `Submission.allard_tc_scf_subspace_submanifold`
- Exact Lean type: `∀ (N n : ℕ) (P : Submodule ℝ (Euclidean N)), Module.finrank ℝ P = n → Chapter02.IsSimonSubmanifold (E := Euclidean n) 2 (P : Set (Euclidean N))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
