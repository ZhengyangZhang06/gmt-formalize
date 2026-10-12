# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.weighted_monotonicity-a1.smoothed_identity-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-weighted-monotonicity-a1-smoothed-identity-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.weighted_monotonicity-a1`
- Child key: `smoothed_identity`
- Declaration: `Submission.weighted_mono_smoothed_identity`
- Exact Lean type: `∀ (n ℓ : ℕ) (μ : Measure (Ambient n ℓ)) (u q G : Ambient n ℓ → ℝ) (φ : ℝ → ℝ) (ξ : Ambient n ℓ) (ε σ ρ R A : ℝ), IsFiniteMeasureOnCompacts μ → 0 < σ → σ ≤ ρ → 0 < ε → (1 + ε) * ρ < R → AEStronglyMeasurable u (μ.restrict (closedBall ξ R)) → AEStronglyMeasurable q (μ.restrict (closedBall ξ R)) → (∀ x ∈ closedBall ξ R, |u x| ≤ A ∧ |q x| ≤ 1) → IntegrableOn G (closedBall ξ R) μ → ContDiff ℝ 1 φ → (∀ t, 1 + ε ≤ t → φ t = 0) → (∀ τ ∈ Icc σ ρ, (n : ℝ) * ∫ x, u x * φ (‖x - ξ‖ / τ) ∂μ + ∫ x, u x * (1 - q x) * (‖x - ξ‖ / τ * deriv φ (‖x - ξ‖ / τ)) ∂μ + ∫ x, φ (‖x - ξ‖ / τ) * G x ∂μ = 0) → (∫ x, u x * φ (‖x - ξ‖ / ρ) ∂μ) / ρ ^ n - (∫ x, u x * φ (‖x - ξ‖ / σ) ∂μ) / σ ^ n = ∫ x, u x * q x * (∫ τ in Ioc σ ρ, -(‖x - ξ‖ / τ ^ 2) * deriv φ (‖x - ξ‖ / τ) / τ ^ n) ∂μ + ∫ τ in Ioc σ ρ, (∫ x, φ (‖x - ξ‖ / τ) * G x ∂μ) / τ ^ (n + 1)`

## Sibling prerequisites

- `root.weighted_monotonicity-a1.cutoff_integral_deriv-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
