# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.moving_blowups-a1.local_comparison-a1.slice_decomposition-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-local-compariso-cc4a50e6b1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.moving_blowups-a1.local_comparison-a1`
- Child key: `slice_decomposition`
- Declaration: `Submission.dimred_mbl_lc_slice_decomposition`
- Exact Lean type: `∀ (P m : ℕ) (C : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)) (Ŝ : ℕ → GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)) (κ : ℕ → Measure (Euclid P)) (K : Set (Euclid P)) (ε : ℝ), IsIntegerMultiplicity C → (∀ j, IsIntegerMultiplicity (Ŝ j)) → (∀ W₀ : Set (Euclid P), IsOpen W₀ → CompactlyContained W₀ univ → ∃ (R : ℕ → GeometricCurrentOn (univ : Set (Euclid P)) (m + 2)) (S' : ℕ → GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)), (∀ j, IsIntegerMultiplicity (R j) ∧ IsIntegerMultiplicity (S' j) ∧ C - Ŝ j - S' j = (R j).boundary) ∧ Tendsto (fun j => (R j).massOn W₀ + (S' j).massOn W₀) atTop (𝓝 0)) → (∀ (T : GeometricCurrentOn (univ : Set (Euclid P)) (m + 2)) (μ μ' : Measure (Euclid P)) (ξ : Euclid P → MultiVector P (m + 2)) (ξ' : Euclid P → MultiVector P (m + 1)) (f : Euclid P → ℝ) (L : NNReal), (∀ K : Set (Euclid P), IsCompact K → μ K < ∞) → (∀ K : Set (Euclid P), IsCompact K → μ' K < ∞) → AEStronglyMeasurable ξ μ → AEStronglyMeasurable ξ' μ' → (∀ᵐ x ∂μ, ∀ α : Covector (Euclid P) (m + 2), |ξ x α| ≤ covectorEuclideanNorm α) → (∀ᵐ x ∂μ', ∀ α : Covector (Euclid P) (m + 1), |ξ' x α| ≤ covectorEuclideanNorm α) → (∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 2), T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) (m + 2)) x) ∂μ) → (∀ η : TestFormOn (univ : Set (Euclid P)) (m + 1), T.boundary η = ∫ x, ξ' x ((η : DifferentialForm (Euclid P) (m + 1)) x) ∂μ') → LipschitzWith L f → ∃ (A : ℝ → GeometricCurrentOn (univ : Set (Euclid P)) (m + 2)) (B : ℝ → GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)), (∀ (t : ℝ) (ω : TestFormOn (univ : Set (Euclid P)) (m + 2)), A t ω = ∫ x in {x | f x < t}, ξ x ((ω : DifferentialForm (Euclid P) (m + 2)) x) ∂μ) ∧ (∀ (t : ℝ) (η : TestFormOn (univ : Set (Euclid P)) (m + 1)), B t η = ∫ x in {x | f x < t}, ξ' x ((η : DifferentialForm (Euclid P) (m + 1)) x) ∂μ') ∧ (∀ (t : ℝ) (η : TestFormOn (univ : Set (Euclid P)) (m + 1)), Disjoint (tsupport (η : DifferentialForm (Euclid P) (m + 1))) {x | f x = t} → (A t).boundary η = B t η) ∧ ∀ (W : Set (Euclid P)) (t : ℝ), IsOpen W → ((A t).boundary - B t).massOn W ≤ (L : ℝ≥0∞) * liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * μ (W ∩ {x | t - h < f x ∧ f x < t})) (𝓝[>] 0)) → (∀ R : GeometricCurrentOn (univ : Set (Euclid P)) (m + 2), IsIntegerMultiplicity R → (∀ W : Set (Euclid P), IsOpen W → CompactlyContained W univ → R.boundary.massOn W < ∞) → IsIntegerMultiplicity R.boundary) → (∀ r : ℝ, ∀ᶠ j in atTop, κ j (ball 0 r) ≠ ∞) → IsCompact K → 0 < ε → ∃ (W F : Set (Euclid P)) (φ' : ℕ → ℕ) (e : ℕ → ℝ≥0∞) (Ŷ Sr : ℕ → GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)), IsOpen W ∧ IsCompact F ∧ K ⊆ W ∧ W ⊆ F ∧ W ⊆ thickening ε K ∧ StrictMono φ' ∧ Tendsto e atTop (𝓝 0) ∧ ∀ i, IsIntegerMultiplicity (Ŷ i) ∧ (Ŷ i).boundary = 0 ∧ (Ŷ i).support ⊆ F ∧ (Sr i).mass ≤ e i ∧ (∀ R : IMRep (univ : Set (Euclid P)) (m + 1), R.Represents (Ŷ i) → R.measure (F \ W) ≤ e i) ∧ κ (φ' i) (F \ W) = 0 ∧ ∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 1), tsupport (ω : DifferentialForm (Euclid P) (m + 1)) ⊆ W → C ω = Ŝ (φ' i) ω + Ŷ i ω + Sr i ω`

## Sibling prerequisites

- `root.density_one_implies_regular-a1.imrep_mass_and_support-a1`
- `root.compactness_of_minimizing_currents-a1.im_calculus-a1`
- `root.compactness_of_minimizing_currents-a1.local_comparison-a1.imrep_restriction-a1`
- `root.compactness_of_minimizing_currents-a1.local_comparison-a1.mass_triangle-a1`
- `root.compactness_of_minimizing_currents-a1.local_comparison-a1.compact_outer_bound-a1`
- `root.compactness_of_minimizing_currents-a1.local_comparison-a1.mass_localization-a1`
- `root.compactness_of_minimizing_currents-a1.local_comparison-a1.good_slice_level-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
