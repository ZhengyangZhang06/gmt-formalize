# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.density_gap-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-density-gap-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1`
- Child key: `density_gap`
- Declaration: `Submission.dimred_cone_density_gap`
- Exact Lean type: `∀ (P j : ℕ), 1 ≤ j → ∃ δ : ℝ, 0 < δ ∧ ∀ (C : GeometricCurrentOn (univ : Set (Euclid P)) j) (θ : ℝ), IsMinimizingIn C univ → BoundaryVanishes C → IsConeCurrent C → HasMassDensity C 0 θ → θ < 1 + δ → θ ≤ 1`

## Sibling prerequisites

- `root.dimension_reduction_results-a1.im_mass_measure-a1`
- `root.dimension_reduction_results-a1.regular_point_density-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
