# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.affine_approximation-a1.lp_monotonicity-a1.cutoff_squeeze-a1.derivative_squeeze-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-affine-approximation-a1-lp-monotonicity-a1-cutoff-squeeze-a1-der-7ff5d3b965/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.affine_approximation-a1.lp_monotonicity-a1.cutoff_squeeze-a1`
- Child key: `derivative_squeeze`
- Declaration: `Submission.aal_cfs_squeeze_of_deriv`
- Exact Lean type: `∀ (n ℓ : ℕ) (μ : Measure (Amb n ℓ)) (w : Amb n ℓ → ℝ) (y : Amb n ℓ) (φ Ψ F : ℝ → ℝ) (S ε c σ ρ : ℝ), 0 < ε → μ (closedBall y S) < ⊤ → AEStronglyMeasurable w μ → (∀ᵐ x ∂μ, 0 ≤ w x ∧ w x ≤ 1) → ContDiff ℝ 1 φ → Antitone φ → (∀ s : ℝ, s ≤ 1 → φ s = 1) → (∀ s : ℝ, 1 + ε ≤ s → φ s = 0) → 0 < σ → σ ≤ ρ → (1 + ε) * ρ < S → (∀ t : ℝ, σ ≤ t → t ≤ ρ → Real.exp (-c) ≤ F t ∧ F t ≤ Real.exp c) → (∀ t : ℝ, σ ≤ t → t ≤ ρ → HasDerivAt Ψ (F t * ((-(∫ x, ‖x - y‖ / t * deriv φ (‖x - y‖ / t) * w x ∂μ) / t) / t ^ n)) t) → Real.exp (-c) * ∫ x, (φ (‖x - y‖ / ρ) - φ (‖x - y‖ / σ)) * (w x / ‖x - y‖ ^ n) ∂μ ≤ Ψ ρ - Ψ σ ∧ Ψ ρ - Ψ σ ≤ Real.exp c * (1 + ε) ^ n * ∫ x, (φ (‖x - y‖ / ρ) - φ (‖x - y‖ / σ)) * (w x / ‖x - y‖ ^ n) ∂μ`

## Sibling prerequisites

- `root.affine_approximation-a1.lp_monotonicity-a1.cutoff_squeeze-a1.cutoff_derivative-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
