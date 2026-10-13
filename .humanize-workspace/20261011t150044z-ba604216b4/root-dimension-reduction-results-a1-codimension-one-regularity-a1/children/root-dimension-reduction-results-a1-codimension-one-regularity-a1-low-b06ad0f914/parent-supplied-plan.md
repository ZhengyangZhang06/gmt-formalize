# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.low_density_regular-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-low-b06ad0f914/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1`
- Child key: `low_density_regular`
- Declaration: `Submission.codim1_low_density_points_regular`
- Exact Lean type: `(∀ (P n : ℕ), 1 ≤ n → ∃ δ : ℝ, 0 < δ ∧ ∀ (d : ℕ) (U N : Set (Euclid P)) (T : GeometricCurrentOn U n), n ≤ d → d ≤ P → IsOpen U → IsEmbeddedSubmanifold 2 d N → (closure N \ N) ∩ U = ∅ → IsMinimizingIn T (U ∩ N) → T.support ⊆ U ∩ N → BoundaryVanishes T → ∀ x ∈ T.support, ∀ θ : ℝ, HasMassDensity T x θ → θ < 1 + δ → x ∈ regularSet T)`

## Sibling prerequisites

- `root.density_and_tangent_cones-a1.vanish_off_support-a1`
- `root.dimension_reduction_results-a1.codimension_one_regularity-a1.oriented_piece_mass-a1`
- `root.density_one_implies_regular-a1.imrep_mass_and_support-a1.unit_orientation_duality-a1`
- `root.regular_set_dense-a1.integer_combination-a1.orientation_sign-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
