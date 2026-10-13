# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.allard_regularity-a1.density_bounds-a1.annular_monotonicity-a1.fixed_cutoff-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-regularity-a1-density-bounds-a1-annular-monotonicity-a1-f-98909e56b4/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.allard_regularity-a1.density_bounds-a1.annular_monotonicity-a1`
- Child key: `fixed_cutoff`
- Declaration: `Submission.allard52_am_fixed_cutoff`
- Exact Lean type: `∀ (n ℓ : ℕ), 1 ≤ n → ∀ p : ℝ, (n : ℝ) < p → ∀ (μ : Measure (Amb n ℓ)) (H : Amb n ℓ → Amb n ℓ) (w : Amb n ℓ → ℝ) (y : Amb n ℓ) (R Λ ε : ℝ) (φ : ℝ → ℝ) (I E a : ℝ → ℝ), 0 < R → 0 < Λ → 0 < ε → ε ≤ 1 → μ (closedBall y R) < ⊤ → IntegrableOn H (closedBall y R) μ → (ENNReal.ofReal (R ^ (p - n)) * ∫⁻ x in closedBall y R, ‖H x‖ₑ ^ p ∂μ) ^ (1 / p) ≤ ENNReal.ofReal ((p - n) / (4 * p) * Λ) → AEStronglyMeasurable w (μ.restrict (ball y R)) → (∀ᵐ x ∂μ, x ∈ ball y R → 0 ≤ w x ∧ w x ≤ 1) → ContDiff ℝ 1 φ → Antitone φ → (∀ u : ℝ, u ≤ 1 → φ u = 1) → (∀ u : ℝ, 1 + ε ≤ u → φ u = 0) → (∀ ρ : ℝ, 0 < ρ → (1 + ε) * ρ < R → ∫ x, ((n : ℝ) * φ (‖x - y‖ / ρ) + ‖x - y‖ / ρ * deriv φ (‖x - y‖ / ρ) * (1 - w x)) ∂μ = -∫ x, φ (‖x - y‖ / ρ) * inner ℝ (x - y) (H x) ∂μ) → (∀ t, I t = ∫ x, φ (‖x - y‖ / t) ∂μ) → (∀ t, E t = ∫ x, φ (‖x - y‖ / t) * inner ℝ (x - y) (H x) ∂μ) → (∀ t, a t = E t / t ^ (n + 1) / (1 + I t / t ^ n)) → (∀ t : ℝ, 0 < t → (1 + ε) * t < R → ContinuousAt a t ∧ |a t| ≤ 2 * ((p - n) / (4 * p)) * Λ / R * (t / R) ^ (-((n : ℝ) / p))) ∧ ∀ s r : ℝ, 0 < s → s ≤ r → (1 + ε) * r < R → Real.exp (-∫ τ in (0)..s, a τ) * (1 + I s / s ^ n) ≤ Real.exp (-∫ τ in (0)..r, a τ) * (1 + I r / r ^ n) ∧ ∫⁻ x in closedBall y r \ ball y ((1 + ε) * s), ENNReal.ofReal (w x / ‖x - y‖ ^ n) ∂μ ≤ ENNReal.ofReal (Real.exp (Λ / 2) * (Real.exp (-∫ τ in (0)..r, a τ) * (1 + I r / r ^ n) - Real.exp (-∫ τ in (0)..s, a τ) * (1 + I s / s ^ n)))`

## Sibling prerequisites

- `root.affine_approximation-a1.lp_monotonicity-a1.curvature_holder-a1`
- `root.allard_regularity-a1.density_bounds-a1.annular_monotonicity-a1.cutoff_calculus-a1`
- `root.allard_regularity-a1.density_bounds-a1.annular_monotonicity-a1.integrating_factor-a1`
- `root.allard_regularity-a1.density_bounds-a1.annular_monotonicity-a1.annular_tonelli-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
