# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.two_dim_cone_density-a1.planes_union_vertex_density-a1.density_of_ball_mass-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-6b39e6ddd7/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.two_dim_cone_density-a1.planes_union_vertex_density-a1`
- Child key: `density_of_ball_mass`
- Declaration: `Submission.idtp_tdc_puvd_density_of_ball_mass`
- Exact Lean type: `∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (x : Euclid P) (θ r : ℝ), 0 ≤ θ → 0 < r → (∀ ρ : ℝ, 0 < ρ → ρ < r → T.massOn (ball x ρ) = ENNReal.ofReal θ * (unitBallVolume n * ENNReal.ofReal (ρ ^ n))) → HasMassDensity T x θ`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
