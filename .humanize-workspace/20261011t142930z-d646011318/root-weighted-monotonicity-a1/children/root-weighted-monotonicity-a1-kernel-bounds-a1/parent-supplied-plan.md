# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.weighted_monotonicity-a1.kernel_bounds-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-weighted-monotonicity-a1-kernel-bounds-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.weighted_monotonicity-a1`
- Child key: `kernel_bounds`
- Declaration: `Submission.weighted_mono_kernel_bounds`
- Exact Lean type: `∀ (n : ℕ) (φ : ℝ → ℝ) (ε σ ρ s : ℝ), ContDiff ℝ 1 φ → Antitone φ → (∀ t, t ≤ 1 → φ t = 1) → (∀ t, 1 + ε ≤ t → φ t = 0) → 0 < ε → 0 < σ → σ ≤ ρ → 0 < s → (φ (s / ρ) - φ (s / σ)) / s ^ n ≤ ∫ τ in Ioc σ ρ, -(s / τ ^ 2) * deriv φ (s / τ) / τ ^ n ∧ ∫ τ in Ioc σ ρ, -(s / τ ^ 2) * deriv φ (s / τ) / τ ^ n ≤ (1 + ε) ^ n * ((φ (s / ρ) - φ (s / σ)) / s ^ n)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
