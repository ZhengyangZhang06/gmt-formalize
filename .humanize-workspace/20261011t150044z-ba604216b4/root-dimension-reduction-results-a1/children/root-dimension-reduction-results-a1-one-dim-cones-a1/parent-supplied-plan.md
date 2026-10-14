# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.one_dim_cones-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-one-dim-cones-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1`
- Child key: `one_dim_cones`
- Declaration: `Submission.dimred_one_dim_minimizing_cone`
- Exact Lean type: `∀ (P : ℕ) (C : GeometricCurrentOn (univ : Set (Euclid P)) 1), IsMinimizingIn C univ → BoundaryVanishes C → IsConeCurrent C → ∃ (e : Euclid P) (m : ℕ), (0 < m → ‖e‖ = 1) ∧ C.support ⊆ (Submodule.span ℝ {e} : Set (Euclid P)) ∧ ∀ y ∈ Submodule.span ℝ {e}, HasMassDensity C y m`

## Sibling prerequisites

- `root.dimension_reduction_results-a1.im_mass_measure-a1`
- `root.dimension_reduction_results-a1.monotonicity-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
