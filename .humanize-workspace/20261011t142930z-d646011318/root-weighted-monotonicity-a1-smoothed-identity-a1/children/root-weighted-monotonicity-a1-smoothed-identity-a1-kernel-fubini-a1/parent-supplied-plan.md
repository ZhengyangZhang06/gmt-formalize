# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.weighted_monotonicity-a1.smoothed_identity-a1.kernel_fubini-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-weighted-monotonicity-a1-smoothed-identity-a1-kernel-fubini-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.weighted_monotonicity-a1.smoothed_identity-a1`
- Child key: `kernel_fubini`
- Declaration: `Submission.wm_smoothed_kernel_fubini`
- Exact Lean type: `∀ (n ℓ k : ℕ) (μ : Measure (Ambient n ℓ)) (w : Ambient n ℓ → ℝ) (χ : ℝ → ℝ) (ξ : Ambient n ℓ) (c σ ρ R A : ℝ), IsFiniteMeasureOnCompacts μ → 0 < σ → 0 < c → c * ρ < R → AEStronglyMeasurable w (μ.restrict (closedBall ξ R)) → (∀ x ∈ closedBall ξ R, |w x| ≤ A) → Continuous χ → (∀ t, c < t → χ t = 0) → ∫ τ in Ioc σ ρ, (∫ x, w x * (-(‖x - ξ‖ / τ ^ 2) * χ (‖x - ξ‖ / τ)) ∂μ) / τ ^ k = ∫ x, w x * (∫ τ in Ioc σ ρ, -(‖x - ξ‖ / τ ^ 2) * χ (‖x - ξ‖ / τ) / τ ^ k) ∂μ`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
