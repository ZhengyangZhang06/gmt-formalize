# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.mean_curvature_monotonicity-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-mean-curvature-monotonicity-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1`
- Child key: `mean_curvature_monotonicity`
- Declaration: `Submission.dor_stationary_mean_curvature_monotonicity`
- Exact Lean type: `∀ (n k ℓ : ℕ), ℓ ≤ k → 0 < n → ∀ (U N : Set (Euclid (n + k))) (y₀ : Euclid (n + k)), IsOpen U → IsEmbeddedSubmanifold 2 (n + ℓ) N → (closure N \ N) ∩ U = ∅ → y₀ ∈ N ∩ U → ∃ r₀ κ : ℝ, 0 < r₀ ∧ 0 ≤ κ ∧ closedBall y₀ (3 * r₀) ⊆ U ∧ ∀ (T : GeometricCurrentOn U n) (R : IMRep U n), R.Represents T → T.support ⊆ N → R.IsStationaryAlong N → (∃ H : Euclid (n + k) → Euclid (n + k), AEStronglyMeasurable H R.measure ∧ (∀ x, ‖H x‖ ≤ κ) ∧ ∀ X : Euclid (n + k) → Euclid (n + k), ContDiff ℝ 1 X → HasCompactSupport X → tsupport X ⊆ ball y₀ (2 * r₀) → R.firstVariation X = -∫ x, inner ℝ (X x) (H x) ∂R.measure) ∧ ∀ z ∈ ball y₀ r₀, ∀ σ ρ : ℝ, 0 < σ → σ ≤ ρ → ρ ≤ r₀ → ENNReal.ofReal (Real.exp (κ * σ) / σ ^ n) * R.measure (ball z σ) ≤ ENNReal.ofReal (Real.exp (κ * ρ) / ρ ^ n) * R.measure (ball z ρ)`

## Sibling prerequisites

- `root.density_one_implies_regular-a1.imrep_mass_and_support-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
