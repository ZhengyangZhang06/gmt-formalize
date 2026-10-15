# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.cone_splitting-a1.subspace_projection-a1.projected_mass-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-fba272cc7e/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.cone_splitting-a1.subspace_projection-a1`
- Child key: `projected_mass`
- Declaration: `Submission.idtp_fons_cs_sp_projected_massOn_le`
- Exact Lean type: `∀ (P m : ℕ) (T X S' : GeometricCurrentOn (univ : Set (Euclid P)) m) (RT RX : IMRep (univ : Set (Euclid P)) m) (V : Submodule ℝ (Euclid P)) (K : Set (Euclid P)), RT.Represents T → RX.Represents X → RT.measure ((V : Set (Euclid P))ᶜ) = 0 → IsCompact K → RX.measure Kᶜ = 0 → (∀ ω : TestFormOn (univ : Set (Euclid P)) m, S' ω = T ω + RX.action (affinePullbackForm V.starProjection 0 (ω : DifferentialForm (Euclid P) m))) → ∃ R : IMRep (univ : Set (Euclid P)) m, (∀ ω : TestFormOn (univ : Set (Euclid P)) m, R.action (ω : DifferentialForm (Euclid P) m) = T ω + X ω) ∧ ∀ O : Set (Euclid P), S'.massOn O ≤ R.measure (V.starProjection ⁻¹' O)`

## Sibling prerequisites

- `root.regular_set_dense-a1.integer_combination-a1.combination_construction-a1`
- `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.cone_splitting-a1.subspace_projection-a1.projection_invariance-a1`
- `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.pushforward-a1.orient_comp-a1`
- `root.minimizing_implies_stationary-a1.diffeo_pushforward-a1.pushforward_current-a1.pairing_bound-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
