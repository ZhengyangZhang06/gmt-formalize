# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.cone_splitting-a1.spine_tangency-a1.centre_tangency-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-spine-tangency-b5fabf0f91/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.cone_splitting-a1.spine_tangency-a1`
- Child key: `centre_tangency`
- Declaration: `Submission.dimred_cs_st_tangent_sub_of_ball_ratio`
- Exact Lean type: `∀ (P n : ℕ) (R : IMRep (univ : Set (Euclid P)) n) (z : Euclid P), (∀ X : Euclid P → Euclid P, ContDiff ℝ 1 X → HasCompactSupport X → R.firstVariation X = 0) → (∀ ρ : ℝ, 0 < ρ → R.measure (closedBall z ρ) = ENNReal.ofReal (ρ ^ n) * R.measure (closedBall z 1)) → ∀ᵐ x ∂R.measure, (approxTangentPlane n R.carrier x).starProjection (x - z) = x - z`

## Sibling prerequisites

- `root.half_space_cone_lies_in_boundary-a1.tangent_projection_aemeasurable-a1`
- `root.density_and_tangent_cones-a1.cone-a1.monotonicity_identity-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
