# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.minimality_transfer-a1.cube_cycle-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-split-off-spine-b5018a2916/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.minimality_transfer-a1`
- Child key: `cube_cycle`
- Declaration: `Submission.dimred_cs_sos_mt_cube_cycle`
- Exact Lean type: `∀ (P k m n' : ℕ) (g : Fin k → Euclid P) (h : n' = k + m) (X : GeometricCurrentOn (univ : Set (Euclid P)) m) (Y : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)) (r : ℝ), 0 < k → 0 < m → Orthonormal ℝ g → IsIntegerMultiplicity X → IsIntegerMultiplicity Y → Y.boundary = X → IsCompact Y.support → Y.support ⊆ ((Submodule.span ℝ (Set.range g))ᗮ : Set (Euclid P)) → 0 < r → ∃ Z E' : GeometricCurrentOn (univ : Set (Euclid P)) n', IsIntegerMultiplicity Z ∧ BoundaryVanishes Z ∧ IsCompact Z.support ∧ Z.support ⊆ {x | ∀ i, |inner ℝ (g i) x| ≤ r} ∩ (Submodule.span ℝ (Set.range g))ᗮ.starProjection ⁻¹' Y.support ∧ E'.mass ≤ ENNReal.ofReal (2 * (k : ℝ) * (2 * r) ^ (k - 1)) * Y.mass ∧ ∀ flat : Covector (Euclid P) n' → Covector (Euclid P) m, (∀ (α : Covector (Euclid P) n') (v : Fin m → Euclid P), flat α v = α (Fin.append g v ∘ Fin.cast h)) → ∀ ω : TestFormOn (univ : Set (Euclid P)) n', Z ω = (∫ t in {t | t ∈ Submodule.span ℝ (Set.range g) ∧ ∀ i, |inner ℝ (g i) t| ≤ r}, currentEval X (fun y => flat ((ω : DifferentialForm (Euclid P) n') (t + y))) ∂μHE[k]) + E' ω`

## Sibling prerequisites

- `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.cone_splitting-a1.split_off_spine-a1.product_current-a1`
- `root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.minimality_transfer-a1.interior_product-a1`
- `root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.minimality_transfer-a1.cube_stokes-a1`
- `root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.minimality_transfer-a1.face_currents-a1`
- `root.compactness_of_minimizing_currents-a1.local_comparison-a1.mass_triangle-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
