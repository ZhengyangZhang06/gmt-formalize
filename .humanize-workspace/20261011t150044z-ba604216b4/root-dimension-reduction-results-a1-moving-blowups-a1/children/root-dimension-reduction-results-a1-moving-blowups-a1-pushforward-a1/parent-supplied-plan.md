# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.moving_blowups-a1.pushforward-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-pushforward-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.moving_blowups-a1`
- Child key: `pushforward`
- Declaration: `Submission.dimred_mbl_pushforward`
- Exact Lean type: `∀ (P m : ℕ) (O : Set (Euclid P)) (f : Euclid P → Euclid P) (L : ℝ), IsOpen O → ContDiffOn ℝ 1 f O → (∀ y ∈ O, ‖fderiv ℝ f y‖ ≤ L) → ∃ push : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1) → GeometricCurrentOn (univ : Set (Euclid P)) (m + 1), (∀ (Y : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)) (R : IMRep (univ : Set (Euclid P)) (m + 1)), R.Represents Y → IsCompact Y.support → Y.support ⊆ O → (∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 1), push Y ω = ∫ x in R.carrier, (R.mult x : ℝ) * R.orient x (((ω : DifferentialForm (Euclid P) (m + 1)) (f x)).compContinuousLinearMap (fderiv ℝ f x)) ∂μHE[m + 1]) ∧ IsIntegerMultiplicity (push Y) ∧ (push Y).support ⊆ f '' Y.support ∧ (push Y).mass ≤ ENNReal.ofReal (L ^ (m + 1)) * Y.mass ∧ (Y.boundary = 0 → (push Y).boundary = 0) ∧ ((∀ y ∈ Y.support, f y = y) → push Y = Y)) ∧ ∀ Y₁ Y₂ : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1), IsIntegerMultiplicity Y₁ → IsIntegerMultiplicity Y₂ → IsCompact Y₁.support → Y₁.support ⊆ O → IsCompact Y₂.support → Y₂.support ⊆ O → push (Y₁ - Y₂) = push Y₁ - push Y₂`

## Sibling prerequisites

- `root.density_and_tangent_cones-a1.vanish_off_support-a1`
- `root.density_one_implies_regular-a1.imrep_mass_and_support-a1`
- `root.dimension_reduction_results-a1.moving_blowups-a1.foundations-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
