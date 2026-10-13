# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.monotonicity_density-a1.stationary_identity-a1.density_limit-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-monotonicity-density-a1-stationary-identity-a1-density-limit-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.monotonicity_density-a1.stationary_identity-a1`
- Child key: `density_limit`
- Declaration: `Submission.annular_identity_limit_at_zero`
- Exact Lean type: `∀ (P : ℝ → ℝ≥0∞) (D : ℝ → ℝ → ℝ≥0∞) (T : ℝ → ℝ≥0∞) (ρ₀ : ℝ), 0 < ρ₀ → (∀ σ ρ : ℝ, 0 < σ → σ ≤ ρ → ρ < ρ₀ → P σ + D σ ρ = P ρ) → (∀ ρ : ℝ, 0 < ρ → ρ < ρ₀ → Tendsto (fun σ : ℝ ↦ D σ ρ) (𝓝[>] 0) (𝓝 (T ρ))) → ∃ θ : ℝ≥0∞, Tendsto P (𝓝[>] 0) (𝓝 θ) ∧ ∀ ρ : ℝ, 0 < ρ → ρ < ρ₀ → θ + T ρ = P ρ`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
