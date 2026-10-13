# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_and_tangent_cones-a1.cone-a1.radial_tangency-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-cone-a1-radial-tangency-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_and_tangent_cones-a1.cone-a1`
- Child key: `radial_tangency`
- Declaration: `Submission.dtc_cone_radial_tangency`
- Exact Lean type: `∀ (P n : ℕ) (R : IMRep (univ : Set (Euclid P)) n) (a : ℝ≥0∞), (∀ X : Euclid P → Euclid P, ContDiff ℝ 1 X → HasCompactSupport X → R.firstVariation X = 0) → (∀ ρ : ℝ, 0 < ρ → R.measure (ball 0 ρ) = a * ENNReal.ofReal (ρ ^ n)) → ∀ᵐ x ∂R.measure, (approxTangentPlane n R.carrier x).starProjection x = x`

## Sibling prerequisites

- `root.density_and_tangent_cones-a1.cone-a1.tangent_projection_measurable-a1`
- `root.density_and_tangent_cones-a1.cone-a1.monotonicity_identity-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
