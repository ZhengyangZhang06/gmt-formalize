# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.affine_approximation-a1.lp_monotonicity-a1.monotonicity_core-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-affine-approximation-a1-lp-monotonicity-a1-monotonicity-core-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.affine_approximation-a1.lp_monotonicity-a1`
- Child key: `monotonicity_core`
- Declaration: `Submission.aal_monotonicity_of_radial_identity`
- Exact Lean type: `∀ (n ℓ : ℕ), 1 ≤ n → ∀ p : ℝ, (n : ℝ) < p → ∀ (μ : Measure (Amb n ℓ)) (H : Amb n ℓ → Amb n ℓ) (w : Amb n ℓ → ℝ) (y : Amb n ℓ) (R S Λ : ℝ), 0 < R → R < S → 0 < Λ → μ (closedBall y S) < ⊤ → AEStronglyMeasurable w μ → (∀ᵐ x ∂μ, 0 ≤ w x ∧ w x ≤ 1) → IntegrableOn H (closedBall y S) μ → ∫⁻ x in closedBall y S, ‖H x‖ₑ ^ p ∂μ < ⊤ → (ENNReal.ofReal (R ^ (p - n)) * ∫⁻ x in closedBall y R, ‖H x‖ₑ ^ p ∂μ) ^ (1 / p) ≤ ENNReal.ofReal ((p - n) / (4 * p) * Λ) → (∀ (φ : ℝ → ℝ) (T ρ : ℝ), ContDiff ℝ 1 φ → (∀ t : ℝ, t ≤ 1 → φ t = 1) → (∀ t : ℝ, T ≤ t → φ t = 0) → 0 < ρ → T * ρ ≤ S → ∫ x, ((n : ℝ) * φ (‖x - y‖ / ρ) + ‖x - y‖ / ρ * deriv φ (‖x - y‖ / ρ) * (1 - w x)) ∂μ = -∫ x, φ (‖x - y‖ / ρ) * inner ℝ (x - y) (H x) ∂μ) → ∃ F : ℝ → ℝ, (∀ r : ℝ, 0 < r → r ≤ R → Real.exp (-Λ) ≤ F r ∧ F r ≤ Real.exp Λ ∧ |F r - 1| ≤ Real.exp (Λ / 2) / 2 * Λ * (r / R) ^ (1 - (n : ℝ) / p) ∧ (Λ ≤ 1 → |F r - 1| ≤ Λ * (r / R) ^ (1 - (n : ℝ) / p))) ∧ (∀ s r : ℝ, 0 < s → s ≤ r → r ≤ R → IntegrableOn (fun x => w x / ‖x - y‖ ^ n) (closedBall y r \ closedBall y s) μ ∧ Real.exp (-Λ) * ∫ x in closedBall y r \ closedBall y s, w x / ‖x - y‖ ^ n ∂μ ≤ (F r * ((μ (closedBall y r)).toReal / r ^ n) + (F r - 1)) - (F s * ((μ (closedBall y s)).toReal / s ^ n) + (F s - 1)) ∧ (F r * ((μ (closedBall y r)).toReal / r ^ n) + (F r - 1)) - (F s * ((μ (closedBall y s)).toReal / s ^ n) + (F s - 1)) ≤ Real.exp Λ * ∫ x in closedBall y r \ closedBall y s, w x / ‖x - y‖ ^ n ∂μ)`

## Sibling prerequisites

- `root.affine_approximation-a1.lp_monotonicity-a1.curvature_holder-a1`
- `root.affine_approximation-a1.lp_monotonicity-a1.cutoff_squeeze-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
