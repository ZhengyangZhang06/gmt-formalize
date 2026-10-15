# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.mass_lower_bound-a1.univ_monotonicity_density-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-6b9e25a71f/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.mass_lower_bound-a1`
- Child key: `univ_monotonicity_density`
- Declaration: `Submission.idtp_cse_mlb_univ_monotonicity_density`
- Exact Lean type: `∀ (P n : ℕ) (C : GeometricCurrentOn (univ : Set (Euclid P)) n), IsMinimizingIn C univ → BoundaryVanishes C → (∀ y : Euclid P, MonotoneOn (fun ρ : ℝ => ENNReal.ofReal (1 / ρ ^ n) * C.massOn (ball y ρ)) (Ioi 0)) ∧ (∃ Θ : Euclid P → ℝ, (∀ y : Euclid P, HasMassDensity C y (Θ y)) ∧ UpperSemicontinuous Θ) ∧ ∀ y ∈ C.support, ∀ θ : ℝ, HasMassDensity C y θ → 1 ≤ θ`

## Sibling prerequisites

- `root.minimizing_implies_stationary-a1.stationary_of_minimizing-a1`
- `root.density_one_implies_regular-a1.mean_curvature_monotonicity-a1.exp_monotonicity-a1`
- `root.density_one_implies_regular-a1.mean_curvature_monotonicity-a1.tangent_projection_measurable-a1`
- `root.dimension_reduction_results-a1.im_mass_measure-a1`
- `root.dimension_reduction_results-a1.monotonicity-a1.density_usc-a1`
- `root.dimension_reduction_results-a1.monotonicity-a1.ae_density_lower_bound-a1`
- `root.dimension_reduction_results-a1.monotonicity-a1.support_density_lower_bound-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
