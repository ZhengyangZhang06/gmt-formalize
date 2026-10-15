# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.minimality_transfer-a1.competitor_mass-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-split-off-spine-8a972d0014/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.minimality_transfer-a1`
- Child key: `competitor_mass`
- Declaration: `Submission.dimred_cs_sos_mt_competitor_mass`
- Exact Lean type: `∀ (P k m n : ℕ) (g : Fin k → Euclid P) (h : n = k + m) (G : Submodule ℝ (Euclid P)) (S : GeometricCurrentOn (univ : Set (Euclid P)) n) (R : IMRep (univ : Set (Euclid P)) n) (S₀ S₀' : GeometricCurrentOn (univ : Set (Euclid P)) m) (R₀ R₀' : IMRep (univ : Set (Euclid P)) m) (W₀ K : Set (Euclid P)) (Z E' : GeometricCurrentOn (univ : Set (Euclid P)) n) (r : ℝ), 0 < k → 0 < m → Orthonormal ℝ g → Submodule.span ℝ (Set.range g) = G → IsMinimizingIn S univ → R.Represents S → R₀.Represents S₀ → R₀'.Represents S₀' → R₀.measure (Gᗮ : Set (Euclid P))ᶜ = 0 → (∀ A : Set (Euclid P), MeasurableSet A → R.measure A = ∫⁻ t in (G : Set (Euclid P)), R₀.measure ((fun y => t + y) ⁻¹' A) ∂μHE[k]) → (∀ flat : Covector (Euclid P) n → Covector (Euclid P) m, (∀ (α : Covector (Euclid P) n) (v : Fin m → Euclid P), flat α v = α (Fin.append g v ∘ Fin.cast h)) → ∀ ω : TestFormOn (univ : Set (Euclid P)) n, S ω = ∫ t in (G : Set (Euclid P)), currentEval S₀ (fun y => flat ((ω : DifferentialForm (Euclid P) n) (t + y))) ∂μHE[k]) → IsOpen W₀ → IsCompact (closure W₀) → (S₀' - S₀).support ⊆ (Gᗮ : Set (Euclid P)) ∩ W₀ → IsCompact K → 0 < r → IsIntegerMultiplicity Z → BoundaryVanishes Z → IsCompact Z.support → Z.support ⊆ {x | ∀ i, |inner ℝ (g i) x| ≤ r} ∩ (Submodule.span ℝ (Set.range g))ᗮ.starProjection ⁻¹' K → (∀ flat : Covector (Euclid P) n → Covector (Euclid P) m, (∀ (α : Covector (Euclid P) n) (v : Fin m → Euclid P), flat α v = α (Fin.append g v ∘ Fin.cast h)) → ∀ ω : TestFormOn (univ : Set (Euclid P)) n, Z ω = (∫ t in {t | t ∈ Submodule.span ℝ (Set.range g) ∧ ∀ i, |inner ℝ (g i) t| ≤ r}, currentEval (S₀' - S₀) (fun y => flat ((ω : DifferentialForm (Euclid P) n) (t + y))) ∂μHE[k]) + E' ω) → ENNReal.ofReal ((2 * r) ^ k) * S₀.massOn W₀ ≤ ENNReal.ofReal ((2 * r) ^ k) * S₀'.massOn W₀ + E'.mass`

## Sibling prerequisites

- `root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.minimality_transfer-a1.interior_product-a1`
- `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.cone_splitting-a1.split_off_spine-a1.product_current-a1`
- `root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.minimality_transfer-a1.slice_integrable-a1`
- `root.compactness_of_minimizing_currents-a1.local_comparison-a1.mass_triangle-a1`
- `root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.minimality_transfer-a1.product_box_measure-a1`
- `root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.minimality_transfer-a1.frame_measure-a1`
- `root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.minimality_transfer-a1.measure_comparison-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
