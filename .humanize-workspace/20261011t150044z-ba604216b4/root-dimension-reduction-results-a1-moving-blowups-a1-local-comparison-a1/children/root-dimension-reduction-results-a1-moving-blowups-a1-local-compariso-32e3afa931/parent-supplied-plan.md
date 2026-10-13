# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.moving_blowups-a1.local_comparison-a1.index_comparison-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-local-compariso-32e3afa931/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.moving_blowups-a1.local_comparison-a1`
- Child key: `index_comparison`
- Declaration: `Submission.dimred_mbl_lc_index_comparison`
- Exact Lean type: `∀ (P m : ℕ) (U A W F : Set (Euclid P)) (T : GeometricCurrentOn U (m + 1)) (R : IMRep U (m + 1)) (C S Ŷ Sr : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)) (π : Euclid P → Euclid P) (G G₃ L : ℝ) (e : ℝ≥0∞), IsOpen U → IsMinimizingIn T A → T.support ⊆ A → R.Represents T → 0 < G → 2 * G ≤ G₃ → closedBall (0 : Euclid P) G₃ ⊆ U → T.massOn (ball 0 G₃) ≠ ∞ → 1 ≤ L → (A ∩ ball 0 (2 * G) = ∅ ∨ (ContDiffOn ℝ 1 π (ball 0 (2 * G)) ∧ MapsTo π (ball 0 (2 * G)) (A ∩ ball 0 G₃) ∧ (∀ y ∈ A ∩ ball 0 (2 * G), π y = y) ∧ ∀ y ∈ ball (0 : Euclid P) (2 * G), ‖fderiv ℝ π y‖ ≤ L)) → IsOpen W → IsCompact F → W ⊆ F → F ⊆ ball 0 G → R.measure (F \ W) = 0 → IsIntegerMultiplicity C → IsIntegerMultiplicity S → S.boundary = C.boundary → (S - C).support ⊆ W → IsIntegerMultiplicity Ŷ → Ŷ.boundary = 0 → Ŷ.support ⊆ F → (∀ R' : IMRep (univ : Set (Euclid P)) (m + 1), R'.Represents Ŷ → R'.measure (F \ W) ≤ e) → Sr.mass ≤ e → (∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 1), tsupport (ω : DifferentialForm (Euclid P) (m + 1)) ⊆ W → C ω = currentEval T (ω : DifferentialForm (Euclid P) (m + 1)) + Ŷ ω + Sr ω) → (∀ (O : Set (Euclid P)) (f : Euclid P → Euclid P) (c : ℝ), IsOpen O → ContDiffOn ℝ 1 f O → (∀ y ∈ O, ‖fderiv ℝ f y‖ ≤ c) → ∃ push : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1) → GeometricCurrentOn (univ : Set (Euclid P)) (m + 1), (∀ (X : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)) (R : IMRep (univ : Set (Euclid P)) (m + 1)), R.Represents X → IsCompact X.support → X.support ⊆ O → (∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 1), push X ω = ∫ x in R.carrier, (R.mult x : ℝ) * R.orient x (((ω : DifferentialForm (Euclid P) (m + 1)) (f x)).compContinuousLinearMap (fderiv ℝ f x)) ∂μHE[m + 1]) ∧ IsIntegerMultiplicity (push X) ∧ (push X).support ⊆ f '' X.support ∧ (push X).mass ≤ ENNReal.ofReal (c ^ (m + 1)) * X.mass ∧ (X.boundary = 0 → (push X).boundary = 0) ∧ ((∀ y ∈ X.support, f y = y) → push X = X)) ∧ ∀ X₁ X₂ : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1), IsIntegerMultiplicity X₁ → IsIntegerMultiplicity X₂ → IsCompact X₁.support → X₁.support ⊆ O → IsCompact X₂.support → X₂.support ⊆ O → push (X₁ - X₂) = push X₁ - push X₂) → T.massOn W ≤ ENNReal.ofReal (L ^ (m + 1)) * (S.massOn W + 2 * e) + ENNReal.ofReal (L ^ (m + 1) - 1) * T.massOn (ball 0 G₃)`

## Sibling prerequisites

- `root.density_and_tangent_cones-a1.vanish_off_support-a1`
- `root.density_one_implies_regular-a1.imrep_mass_and_support-a1`
- `root.compactness_of_minimizing_currents-a1.im_calculus-a1`
- `root.density_and_tangent_cones-a1.localize-a1.restrict_im-a1`
- `root.compactness_of_minimizing_currents-a1.local_comparison-a1.mass_triangle-a1`
- `root.compactness_of_minimizing_currents-a1.local_comparison-a1.compact_outer_bound-a1`
- `root.dimension_reduction_results-a1.moving_blowups-a1.local_comparison-a1.retraction_comparison-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
