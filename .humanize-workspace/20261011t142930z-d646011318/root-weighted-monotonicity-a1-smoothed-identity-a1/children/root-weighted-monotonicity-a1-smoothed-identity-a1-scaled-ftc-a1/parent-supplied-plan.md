# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.weighted_monotonicity-a1.smoothed_identity-a1.scaled_ftc-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-weighted-monotonicity-a1-smoothed-identity-a1-scaled-ftc-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.weighted_monotonicity-a1.smoothed_identity-a1`
- Child key: `scaled_ftc`
- Declaration: `Submission.wm_smoothed_scaled_ftc`
- Exact Lean type: `∀ (n : ℕ) (I I₁ J₁ L : ℝ → ℝ) (σ ρ : ℝ), 0 < σ → σ ≤ ρ → (∀ τ ∈ Icc σ ρ, HasDerivAt I (I₁ τ) τ) → (∀ τ ∈ Icc σ ρ, (n : ℝ) * I τ - τ * I₁ τ + τ * J₁ τ + L τ = 0) → ContinuousOn J₁ (Icc σ ρ) → ContinuousOn L (Icc σ ρ) → I ρ / ρ ^ n - I σ / σ ^ n = (∫ τ in Ioc σ ρ, J₁ τ / τ ^ n) + ∫ τ in Ioc σ ρ, L τ / τ ^ (n + 1)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
