# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.area_comparison-a1.piece_pushforward-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-sim-686f3f40d6/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.area_comparison-a1`
- Child key: `piece_pushforward`
- Declaration: `Submission.codim1_ac_oriented_piece_pushforward`
- Exact Lean type: `∀ (P m : ℕ) (N W : Set (Euclid P)) (ξ : Euclid P → MultiVector P m) (Φ : Euclid P → Euclid P) (Λ : NNReal), 1 ≤ m → IsEmbeddedSubmanifold 1 m N → IsOrientation m N ξ → IsOpen W → μHE[m] (N ∩ W) ≠ ∞ → ContDiff ℝ 1 Φ → Bijective Φ → (∀ x, Injective (fderiv ℝ Φ x)) → LipschitzWith Λ Φ → AntilipschitzWith Λ Φ → ∃ D : GeometricCurrentOn (univ : Set (Euclid P)) m, IsIntegerMultiplicity D ∧ (∀ ω : TestFormOn (univ : Set (Euclid P)) m, Integrable (fun x => ξ x (((ω : DifferentialForm (Euclid P) m) (Φ x)).compContinuousLinearMap (fderiv ℝ Φ x))) (μHE[m].restrict (N ∩ W)) ∧ D ω = ∫ x in N ∩ W, ξ x (((ω : DifferentialForm (Euclid P) m) (Φ x)).compContinuousLinearMap (fderiv ℝ Φ x)) ∂μHE[m]) ∧ ∀ W' : Set (Euclid P), D.massOn W' ≤ μHE[m] (Φ '' (N ∩ W) ∩ W')`

## Sibling prerequisites

- `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.area_comparison-a1.image_submanifold-a1`
- `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.area_comparison-a1.submanifold_approx_tangent-a1`
- `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.area_comparison-a1.submanifold_area-a1`
- `root.minimizing_implies_stationary-a1.diffeo_pushforward-a1.orientation_pushforward-a1`
- `root.density_one_implies_regular-a1.imrep_mass_and_support-a1.unit_orientation_duality-a1`
- `root.minimizing_implies_stationary-a1.diffeo_pushforward-a1.pushforward_current-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
