# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.density_gap-a1.first_variation_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-density-gap-a1-first-variation-bound-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.density_gap-a1`
- Child key: `first_variation_bound`
- Declaration: `Submission.dimred_cdg_pushforward_massOn_le_first_variation`
- Exact Lean type: `∀ (P n : ℕ) (U W : Set (Euclid P)) (R : IMRep U n) (X : Euclid P → Euclid P) (φ : ℝ → Euclid P → Euclid P), IsOpen W → R.measure W ≠ ∞ → ContDiff ℝ 1 X → HasCompactSupport X → tsupport X ⊆ W → (∀ t, ContDiff ℝ 1 (φ t)) → (∀ t x, x ∉ tsupport X → φ t x = x) → (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, |t| < δ → ∀ x, ‖fderiv ℝ (φ t) x - ContinuousLinearMap.id ℝ (Euclid P) - t • fderiv ℝ X x‖ ≤ ε * |t|) → ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, |t| < δ → ∀ S : GeometricCurrentOn U n, (∀ ω : TestFormOn U n, S ω = ∫ x in R.carrier, (R.mult x : ℝ) * R.orient x (((ω : DifferentialForm (Euclid P) n) (φ t x)).compContinuousLinearMap (fderiv ℝ (φ t) x)) ∂μHE[n]) → S.massOn W ≤ ENNReal.ofReal ((R.measure W).toReal + t * R.firstVariation X + ε * |t|)`

## Sibling prerequisites

- `root.minimizing_implies_stationary-a1.covector_gram_bounds-a1`
- `root.minimizing_implies_stationary-a1.tangent_projection_measurable-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
