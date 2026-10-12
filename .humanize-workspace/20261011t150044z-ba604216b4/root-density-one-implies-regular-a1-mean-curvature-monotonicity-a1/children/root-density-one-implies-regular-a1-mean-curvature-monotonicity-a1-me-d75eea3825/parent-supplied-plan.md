# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.mean_curvature_monotonicity-a1.mean_curvature_formula-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-mean-curvature-monotonicity-a1-me-d75eea3825/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.mean_curvature_monotonicity-a1`
- Child key: `mean_curvature_formula`
- Declaration: `Submission.dsmc_firstVariation_eq_neg_meanCurvature`
- Exact Lean type: `∀ (P n : ℕ) (U N : Set (Euclid P)) (R : IMRep U n) (Pt : Euclid P → (Euclid P →L[ℝ] Euclid P)) (y₀ : Euclid P) (r β : ℝ), 0 ≤ β → ball y₀ (3 * r) ⊆ U → ContDiffOn ℝ 1 Pt (ball y₀ (3 * r)) → (∀ y ∈ ball y₀ (3 * r), ∀ u w : Euclid P, inner ℝ (Pt y u) w = inner ℝ u (Pt y w)) → (∀ y ∈ ball y₀ (2 * r), ‖fderiv ℝ Pt y‖ ≤ β) → (∀ q ∈ N ∩ ball y₀ (3 * r), ∀ u : Euclid P, Pt q u ∈ tangentSpace N q) → (∀ q ∈ N ∩ ball y₀ (3 * r), ∀ u ∈ tangentSpace N q, Pt q u = u) → (∀ᵐ x ∂R.measure, x ∈ N) → (∀ᵐ x ∂R.measure, x ∈ ball y₀ (3 * r) → (approxTangentPlane n R.carrier x : Set (Euclid P)) ⊆ tangentSpace N x) → AEMeasurable (fun x => (approxTangentPlane n R.carrier x).starProjection) R.measure → R.IsStationaryAlong N → ∃ H : Euclid P → Euclid P, AEStronglyMeasurable H R.measure ∧ (∀ x, ‖H x‖ ≤ (n : ℝ) * β) ∧ ∀ X : Euclid P → Euclid P, ContDiff ℝ 1 X → HasCompactSupport X → tsupport X ⊆ ball y₀ (2 * r) → R.firstVariation X = -∫ x, inner ℝ (X x) (H x) ∂R.measure`

## Sibling prerequisites

- `root.density_one_implies_regular-a1.mean_curvature_monotonicity-a1.first_variation_integral-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
