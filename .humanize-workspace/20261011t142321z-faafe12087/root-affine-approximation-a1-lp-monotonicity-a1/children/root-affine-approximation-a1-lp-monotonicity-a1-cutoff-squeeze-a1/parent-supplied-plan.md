# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.affine_approximation-a1.lp_monotonicity-a1.cutoff_squeeze-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-affine-approximation-a1-lp-monotonicity-a1-cutoff-squeeze-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.affine_approximation-a1.lp_monotonicity-a1`
- Child key: `cutoff_squeeze`
- Declaration: `Submission.aal_cutoff_integrating_factor_squeeze`
- Exact Lean type: `∀ (n ℓ : ℕ) (μ : Measure (Amb n ℓ)) (H : Amb n ℓ → Amb n ℓ) (w : Amb n ℓ → ℝ) (y : Amb n ℓ) (φ : ℝ → ℝ) (I a : ℝ → ℝ) (S ε M β : ℝ), 0 < ε → β < 1 → μ (closedBall y S) < ⊤ → AEStronglyMeasurable w μ → (∀ᵐ x ∂μ, 0 ≤ w x ∧ w x ≤ 1) → IntegrableOn H (closedBall y S) μ → ContDiff ℝ 1 φ → Antitone φ → (∀ t : ℝ, t ≤ 1 → φ t = 1) → (∀ t : ℝ, 1 + ε ≤ t → φ t = 0) → (∀ ρ : ℝ, 0 < ρ → (1 + ε) * ρ ≤ S → ∫ x, ((n : ℝ) * φ (‖x - y‖ / ρ) + ‖x - y‖ / ρ * deriv φ (‖x - y‖ / ρ) * (1 - w x)) ∂μ = -∫ x, φ (‖x - y‖ / ρ) * inner ℝ (x - y) (H x) ∂μ) → (∀ t : ℝ, I t = ∫ x, φ (‖x - y‖ / t) ∂μ) → (∀ t : ℝ, a t = (∫ x, φ (‖x - y‖ / t) * inner ℝ (x - y) (H x) ∂μ) / t ^ (n + 1) / (1 + I t / t ^ n)) → (∀ t : ℝ, 0 < t → (1 + ε) * t < S → |a t| ≤ M * t ^ (-β)) → ∀ σ ρ : ℝ, 0 < σ → σ ≤ ρ → (1 + ε) * ρ < S → Real.exp (-∫ t in (0)..ρ, |a t|) * ∫ x, (φ (‖x - y‖ / ρ) - φ (‖x - y‖ / σ)) * (w x / ‖x - y‖ ^ n) ∂μ ≤ Real.exp (-∫ t in (0)..ρ, a t) * (1 + I ρ / ρ ^ n) - Real.exp (-∫ t in (0)..σ, a t) * (1 + I σ / σ ^ n) ∧ Real.exp (-∫ t in (0)..ρ, a t) * (1 + I ρ / ρ ^ n) - Real.exp (-∫ t in (0)..σ, a t) * (1 + I σ / σ ^ n) ≤ Real.exp (∫ t in (0)..ρ, |a t|) * (1 + ε) ^ n * ∫ x, (φ (‖x - y‖ / ρ) - φ (‖x - y‖ / σ)) * (w x / ‖x - y‖ ^ n) ∂μ`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
