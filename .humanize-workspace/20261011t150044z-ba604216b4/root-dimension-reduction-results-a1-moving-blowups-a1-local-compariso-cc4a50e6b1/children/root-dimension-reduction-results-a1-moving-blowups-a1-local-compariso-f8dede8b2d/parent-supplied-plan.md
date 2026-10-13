# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.moving_blowups-a1.local_comparison-a1.slice_decomposition-a1.level_decomposition-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-local-compariso-f8dede8b2d/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.moving_blowups-a1.local_comparison-a1.slice_decomposition-a1`
- Child key: `level_decomposition`
- Declaration: `Submission.dimred_mbl_lc_sd_level_decomposition`
- Exact Lean type: `∀ (P m : ℕ) (R A : GeometricCurrentOn (univ : Set (Euclid P)) (m + 2)) (B S' : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)) (ρ : IMRep (univ : Set (Euclid P)) (m + 2)) (β : IMRep (univ : Set (Euclid P)) (m + 1)) (f : Euclid P → ℝ) (t : ℝ) (W₀ : Set (Euclid P)) (c : ℝ≥0∞), ρ.Represents R → IsIntegerMultiplicity S' → Continuous f → IsOpen W₀ → IsCompact {x | f x ≤ t} → {x | f x ≤ t} ⊆ W₀ → (∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 2), A ω = ∫ x in {x | f x < t}, ρ.orient x ((ω : DifferentialForm (Euclid P) (m + 2)) x) ∂ρ.measure) → (∀ η : TestFormOn (univ : Set (Euclid P)) (m + 1), B η = ∫ x in {x | f x < t}, β.orient x ((η : DifferentialForm (Euclid P) (m + 1)) x) ∂β.measure) → (∀ η : TestFormOn (univ : Set (Euclid P)) (m + 1), Disjoint (tsupport (η : DifferentialForm (Euclid P) (m + 1))) {x | f x = t} → A.boundary η = B η) → (A.boundary - B).massOn W₀ ≤ c → c ≠ ∞ → (∀ T : GeometricCurrentOn (univ : Set (Euclid P)) (m + 2), IsIntegerMultiplicity T → (∀ W : Set (Euclid P), IsOpen W → CompactlyContained W univ → T.boundary.massOn W < ∞) → IsIntegerMultiplicity T.boundary) → ∃ Y Sr : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1), IsIntegerMultiplicity Y ∧ Y.boundary = 0 ∧ Y.support ⊆ {x | f x ≤ t} ∧ Sr.mass ≤ S'.massOn W₀ + c ∧ (∀ Q : IMRep (univ : Set (Euclid P)) (m + 1), Q.Represents Y → Q.measure {x | f x = t} ≤ c) ∧ ∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 1), tsupport (ω : DifferentialForm (Euclid P) (m + 1)) ⊆ {x | f x < t} → Y ω = R.boundary ω ∧ Sr ω = S' ω`

## Sibling prerequisites

- `root.density_one_implies_regular-a1.imrep_mass_and_support-a1`
- `root.compactness_of_minimizing_currents-a1.im_calculus-a1`
- `root.compactness_of_minimizing_currents-a1.local_comparison-a1.imrep_restriction-a1`
- `root.compactness_of_minimizing_currents-a1.local_comparison-a1.mass_triangle-a1`
- `root.compactness_of_minimizing_currents-a1.local_comparison-a1.compact_outer_bound-a1`
- `root.compactness_of_minimizing_currents-a1.local_comparison-a1.mass_localization-a1`
- `root.regular_set_dense-a1.constant_multiplicity_reduction-a1.support_of_vanishing-a1`
- `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.im_local-a1.imrep_measure-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
