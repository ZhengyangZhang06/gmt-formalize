# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.mean_curvature_monotonicity-a1.exp_monotonicity-a1.cutoff_first_variation-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-mean-curvature-monotonicity-a1-ex-52a2d9a01b/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.mean_curvature_monotonicity-a1.exp_monotonicity-a1`
- Child key: `cutoff_first_variation`
- Declaration: `Submission.dsmc_em_cutoff_first_variation_le`
- Exact Lean type: `∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (H : Euclid P → Euclid P) (κ : ℝ) (z : Euclid P) (r : ℝ) (η : ℝ → ℝ), closedBall z r ⊆ U → AEMeasurable (fun x => (approxTangentPlane n R.carrier x).starProjection) R.measure → (∀ x, ‖H x‖ ≤ κ) → (∀ X : Euclid P → Euclid P, ContDiff ℝ 1 X → HasCompactSupport X → tsupport X ⊆ ball z r → R.firstVariation X = -∫ x, inner ℝ (X x) (H x) ∂R.measure) → ContDiff ℝ 1 η → (∀ u, 0 ≤ η u) → (∀ u, deriv η u ≤ 0) → (∀ u, 1 ≤ u → η u = 0) → ∀ s : ℝ, 0 < s → s < r → (n : ℝ) * ∫ x, η (‖x - z‖ ^ 2 / s ^ 2) ∂R.measure + ∫ x, 2 * (‖x - z‖ ^ 2 / s ^ 2) * deriv η (‖x - z‖ ^ 2 / s ^ 2) ∂R.measure ≤ κ * s * ∫ x, η (‖x - z‖ ^ 2 / s ^ 2) ∂R.measure`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
