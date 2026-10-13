# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.allard_regularity-a1.density_bounds-a1.annular_monotonicity-a1.cutoff_limit-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-regularity-a1-density-bounds-a1-annular-monotonicity-a1-c-e2dbd3c563/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.allard_regularity-a1.density_bounds-a1.annular_monotonicity-a1`
- Child key: `cutoff_limit`
- Declaration: `Submission.allard52_am_cutoff_limit`
- Exact Lean type: `∀ (n ℓ : ℕ), 1 ≤ n → ∀ p : ℝ, (n : ℝ) < p → ∀ (μ : Measure (Amb n ℓ)) (H : Amb n ℓ → Amb n ℓ) (w : Amb n ℓ → ℝ) (y : Amb n ℓ) (R Λ : ℝ), 0 < R → 0 < Λ → Λ ≤ 1 → μ (closedBall y R) < ⊤ → IntegrableOn H (closedBall y R) μ → (ENNReal.ofReal (R ^ (p - n)) * ∫⁻ x in closedBall y R, ‖H x‖ₑ ^ p ∂μ) ^ (1 / p) ≤ ENNReal.ofReal ((p - n) / (4 * p) * Λ) → AEStronglyMeasurable w (μ.restrict (ball y R)) → (∀ᵐ x ∂μ, x ∈ ball y R → 0 ≤ w x ∧ w x ≤ 1) → (∀ (φ : ℝ → ℝ) (T ρ : ℝ), ContDiff ℝ 1 φ → (∀ t : ℝ, t ≤ 1 → φ t = 1) → (∀ t : ℝ, T ≤ t → φ t = 0) → 0 < ρ → T * ρ < R → ∫ x, ((n : ℝ) * φ (‖x - y‖ / ρ) + ‖x - y‖ / ρ * deriv φ (‖x - y‖ / ρ) * (1 - w x)) ∂μ = -∫ x, φ (‖x - y‖ / ρ) * inner ℝ (x - y) (H x) ∂μ) → ∃ F : ℝ → ℝ, (∀ r ∈ Ioo 0 R, Real.exp (-Λ) ≤ F r ∧ F r ≤ Real.exp Λ ∧ |F r - 1| ≤ Λ * (r / R) ^ (1 - (n : ℝ) / p)) ∧ (∀ s r : ℝ, 0 < s → s ≤ r → r < R → F s * (s ^ n)⁻¹ * (μ (closedBall y s)).toReal + F s - 1 ≤ F r * (r ^ n)⁻¹ * (μ (closedBall y r)).toReal + F r - 1 ∧ ∫⁻ x in closedBall y r \ closedBall y s, ENNReal.ofReal (w x / ‖x - y‖ ^ n) ∂μ ≤ ENNReal.ofReal (Real.exp Λ * ((F r * (r ^ n)⁻¹ * (μ (closedBall y r)).toReal + F r - 1) - (F s * (s ^ n)⁻¹ * (μ (closedBall y s)).toReal + F s - 1))))`

## Sibling prerequisites

- `root.allard_regularity-a1.density_bounds-a1.annular_monotonicity-a1.fixed_cutoff-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
