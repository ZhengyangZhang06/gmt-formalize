# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.weighted_monotonicity-a1.smoothed_identity-a1.scale_continuity-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-weighted-monotonicity-a1-smoothed-identity-a1-scale-continuity-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.weighted_monotonicity-a1.smoothed_identity-a1`
- Child key: `scale_continuity`
- Declaration: `Submission.wm_smoothed_scale_integral_continuousOn`
- Exact Lean type: `∀ (n ℓ : ℕ) (μ : Measure (Ambient n ℓ)) (g : Ambient n ℓ → ℝ) (ψ : ℝ → ℝ) (ξ : Ambient n ℓ) (c σ ρ R : ℝ), 0 < σ → 0 < c → c * ρ < R → IntegrableOn g (closedBall ξ R) μ → Continuous ψ → (∀ t, c < t → ψ t = 0) → ContinuousOn (fun τ ↦ ∫ x, g x * ψ (‖x - ξ‖ / τ) ∂μ) (Icc σ ρ)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
