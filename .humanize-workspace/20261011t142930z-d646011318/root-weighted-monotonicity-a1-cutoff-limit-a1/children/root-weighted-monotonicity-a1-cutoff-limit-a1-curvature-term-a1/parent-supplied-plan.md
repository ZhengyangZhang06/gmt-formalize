# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.weighted_monotonicity-a1.cutoff_limit-a1.curvature_term-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-weighted-monotonicity-a1-cutoff-limit-a1-curvature-term-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.weighted_monotonicity-a1.cutoff_limit-a1`
- Child key: `curvature_term`
- Declaration: `Submission.weighted_mono_curvature_term_tendsto`
- Exact Lean type: `∀ (n ℓ : ℕ) (μ : Measure (Ambient n ℓ)) (G : Ambient n ℓ → ℝ) (ξ : Ambient n ℓ) (σ ρ R : ℝ) (φ : ℕ → ℝ → ℝ) (ε : ℕ → ℝ), 0 < σ → σ ≤ ρ → IntegrableOn G (closedBall ξ R) μ → Tendsto ε atTop (𝓝 0) → (∀ m, 0 < ε m) → (∀ m, (1 + ε m) * ρ ≤ R) → (∀ m, Continuous (φ m)) → (∀ m s, 0 ≤ φ m s ∧ φ m s ≤ 1) → (∀ m s, s ≤ 1 → φ m s = 1) → (∀ m s, 1 + ε m ≤ s → φ m s = 0) → IntegrableOn (fun τ ↦ (∫ x in closedBall ξ τ, G x ∂μ) / τ ^ (n + 1)) (Ioc σ ρ) ∧ Tendsto (fun m ↦ ∫ τ in Ioc σ ρ, (∫ x, φ m (‖x - ξ‖ / τ) * G x ∂μ) / τ ^ (n + 1)) atTop (𝓝 (∫ τ in Ioc σ ρ, (∫ x in closedBall ξ τ, G x ∂μ) / τ ^ (n + 1)))`

## Sibling prerequisites

- `root.weighted_monotonicity-a1.cutoff_limit-a1.cutoff_integral-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
