# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.half_space_cone_lies_in_boundary-a1.radial_tangency_of_ball_ratio-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-half-space-cone-lies-in-boundary-a1-radial-tangency-of-ball-ratio-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.half_space_cone_lies_in_boundary-a1`
- Child key: `radial_tangency_of_ball_ratio`
- Declaration: `Submission.stationary_imrep_radial_tangency_of_ball_ratio`
- Exact Lean type: `∀ (P n : ℕ) (R : IMRep (univ : Set (Euclid P)) n), (∀ X : Euclid P → Euclid P, ContDiff ℝ 1 X → HasCompactSupport X → R.firstVariation X = 0) → AEMeasurable (fun x => (approxTangentPlane n R.carrier x).starProjection) R.measure → (∀ ρ : ℝ, 0 < ρ → R.measure (closedBall (0 : Euclid P) ρ) = ENNReal.ofReal (ρ ^ n) * R.measure (closedBall (0 : Euclid P) 1)) → ∀ᵐ x ∂R.measure, (approxTangentPlane n R.carrier x).starProjection x = x`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
