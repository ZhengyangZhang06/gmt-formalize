# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-sim-7577af74dd/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1`
- Child key: `simons_regular_cone`
- Declaration: `Submission.codim1_simons_regular_cone_density`
- Exact Lean type: `∀ (P m : ℕ) (C : GeometricCurrentOn (univ : Set (Euclid P)) m) (A₀ : Submodule ℝ (Euclid P)), 2 ≤ m → m ≤ 6 → Module.finrank ℝ A₀ = m + 1 → IsMinimizingIn C univ → BoundaryVanishes C → IsConeCurrent C → C.support ⊆ (A₀ : Set (Euclid P)) → (∀ y ∈ C.support, y ≠ 0 → y ∈ regularSet C ∧ HasMassDensity C y 1) → ∀ θ : ℝ, HasMassDensity C 0 θ → θ ≤ 1`

## Sibling prerequisites

- `root.density_and_tangent_cones-a1.vanish_off_support-a1`
- `root.half_space_cone_lies_in_boundary-a1.cone_measure_homogeneous-a1.cone_pullback_identity-a1`
- `root.dimension_reduction_results-a1.codimension_one_regularity-a1.oriented_piece_mass-a1`
- `root.density_one_implies_regular-a1.imrep_mass_and_support-a1.unit_orientation_duality-a1`
- `root.regular_set_dense-a1.integer_combination-a1.orientation_sign-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
