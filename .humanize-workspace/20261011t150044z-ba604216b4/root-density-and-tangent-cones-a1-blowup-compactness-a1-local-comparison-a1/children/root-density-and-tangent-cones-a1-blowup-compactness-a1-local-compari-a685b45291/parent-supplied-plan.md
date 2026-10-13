# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.pushforward-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-a685b45291/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1`
- Child key: `pushforward`
- Declaration: `Submission.dtc_bc_lc_pushforward`
- Exact Lean type: `∀ (P m : ℕ) (O : Set (Euclid P)) (f : Euclid P → Euclid P), IsOpen O → ContDiffOn ℝ 1 f O → ∃ push : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1) → GeometricCurrentOn (univ : Set (Euclid P)) (m + 1), (∀ (Y : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)) (R : IMRep (univ : Set (Euclid P)) (m + 1)), R.Represents Y → IsCompact Y.support → Y.support ⊆ O → (∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 1), push Y ω = ∫ x in R.carrier, (R.mult x : ℝ) * R.orient x (((ω : DifferentialForm (Euclid P) (m + 1)) (f x)).compContinuousLinearMap (fderiv ℝ f x)) ∂μHE[m + 1]) ∧ IsIntegerMultiplicity (push Y) ∧ (push Y).support ⊆ f '' Y.support ∧ (∀ L : ℝ, (∀ y ∈ O, ‖fderiv ℝ f y‖ ≤ L) → (push Y).mass ≤ ENNReal.ofReal (L ^ (m + 1)) * Y.mass) ∧ (Y.boundary = 0 → (push Y).boundary = 0)) ∧ ∀ Y₁ Y₂ : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1), IsIntegerMultiplicity Y₁ → IsIntegerMultiplicity Y₂ → IsCompact Y₁.support → Y₁.support ⊆ O → IsCompact Y₂.support → Y₂.support ⊆ O → push (Y₁ - Y₂) = push Y₁ - push Y₂`

## Sibling prerequisites

- `root.compactness_of_minimizing_currents-a1.im_calculus-a1`
- `root.density_and_tangent_cones-a1.mass_eq_measure-a1`
- `root.density_and_tangent_cones-a1.vanish_off_support-a1`
- `root.regular_set_dense-a1.constant_multiplicity_reduction-a1.support_of_vanishing-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
