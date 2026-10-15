# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_tangent_cone_planar-a1.plane_ball_measure-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-3c84739071/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_tangent_cone_planar-a1`
- Child key: `plane_ball_measure`
- Declaration: `Submission.idtp_cttp_span_ball_measure`
- Exact Lean type: `∀ (P n : ℕ) (τ : Fin n → Euclid P), Orthonormal ℝ τ → ∀ y ∈ Submodule.span ℝ (Set.range τ), ∀ ρ : ℝ, 0 < ρ → μHE[n] (ball y ρ ∩ (Submodule.span ℝ (Set.range τ) : Set (Euclid P))) = unitBallVolume n * ENNReal.ofReal (ρ ^ n)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
