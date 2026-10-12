# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.weighted_monotonicity-a1.cutoff_limit-a1.kernel_limit-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-weighted-monotonicity-a1-cutoff-limit-a1-kernel-limit-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.weighted_monotonicity-a1.cutoff_limit-a1`
- Child key: `kernel_limit`
- Declaration: `Submission.weighted_mono_kernel_limit`
- Exact Lean type: `∀ (n : ℕ) (σ ρ : ℝ) (φ : ℕ → ℝ → ℝ) (ε : ℕ → ℝ), 0 < σ → σ ≤ ρ → Tendsto ε atTop (𝓝 0) → (∀ m, 0 < ε m ∧ ε m ≤ 1) → (∀ m, Antitone (φ m)) → (∀ m t, t ≤ 1 → φ m t = 1) → (∀ m t, 1 + ε m ≤ t → φ m t = 0) → (∀ m s, 0 < s → (φ m (s / ρ) - φ m (s / σ)) / s ^ n ≤ ∫ τ in Ioc σ ρ, -(s / τ ^ 2) * deriv (φ m) (s / τ) / τ ^ n ∧ ∫ τ in Ioc σ ρ, -(s / τ ^ 2) * deriv (φ m) (s / τ) / τ ^ n ≤ (1 + ε m) ^ n * ((φ m (s / ρ) - φ m (s / σ)) / s ^ n)) → (∀ m, Measurable (fun s ↦ ∫ τ in Ioc σ ρ, -(s / τ ^ 2) * deriv (φ m) (s / τ) / τ ^ n)) ∧ (∀ m s, 0 ≤ s → |∫ τ in Ioc σ ρ, -(s / τ ^ 2) * deriv (φ m) (s / τ) / τ ^ n| ≤ 2 ^ n / σ ^ n) ∧ (∀ m s, (1 + ε m) * ρ < s → ∫ τ in Ioc σ ρ, -(s / τ ^ 2) * deriv (φ m) (s / τ) / τ ^ n = 0) ∧ (∀ s, 0 ≤ s → Tendsto (fun m ↦ ∫ τ in Ioc σ ρ, -(s / τ ^ 2) * deriv (φ m) (s / τ) / τ ^ n) atTop (𝓝 ((Ioc σ ρ).indicator (fun s ↦ (s ^ n)⁻¹) s)))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
