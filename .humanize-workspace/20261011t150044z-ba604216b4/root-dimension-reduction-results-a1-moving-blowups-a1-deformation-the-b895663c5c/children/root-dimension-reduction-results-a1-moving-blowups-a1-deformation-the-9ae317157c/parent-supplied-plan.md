# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.face_replacement-a1.plane_orientation-a1.tangent_le_plane-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-deformation-the-9ae317157c/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.face_replacement-a1.plane_orientation-a1`
- Child key: `tangent_le_plane`
- Declaration: `Submission.dimred_mbl_dtfrpo_approxTangent_le_of_sub_mem`
- Exact Lean type: `∀ (P n : ℕ) (A : Set (Euclid P)) (x : Euclid P) (Q V : Submodule ℝ (Euclid P)), (∀ a ∈ A, a - x ∈ V) → HasApproximateTangentSpaceAt n A x Q → Q ≤ V`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
