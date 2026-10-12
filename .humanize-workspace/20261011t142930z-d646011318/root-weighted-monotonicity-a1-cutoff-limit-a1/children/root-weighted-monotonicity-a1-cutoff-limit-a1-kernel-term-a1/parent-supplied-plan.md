# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.weighted_monotonicity-a1.cutoff_limit-a1.kernel_term-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-weighted-monotonicity-a1-cutoff-limit-a1-kernel-term-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.weighted_monotonicity-a1.cutoff_limit-a1`
- Child key: `kernel_term`
- Declaration: `Submission.weighted_mono_kernel_term_tendsto`
- Exact Lean type: `∀ (n ℓ : ℕ) (μ : Measure (Ambient n ℓ)) (u q : Ambient n ℓ → ℝ) (ξ : Ambient n ℓ) (σ ρ R A C : ℝ) (k : ℕ → ℝ → ℝ), IsFiniteMeasureOnCompacts μ → 0 < σ → ρ ≤ R → AEStronglyMeasurable u (μ.restrict (closedBall ξ R)) → AEStronglyMeasurable q (μ.restrict (closedBall ξ R)) → (∀ x ∈ closedBall ξ R, |u x| ≤ A ∧ |q x| ≤ 1) → (∀ m, Measurable (k m)) → (∀ m s, 0 ≤ s → |k m s| ≤ C) → (∀ m s, R < s → k m s = 0) → (∀ s, 0 ≤ s → Tendsto (fun m ↦ k m s) atTop (𝓝 ((Ioc σ ρ).indicator (fun s ↦ (s ^ n)⁻¹) s))) → IntegrableOn (fun x ↦ u x * (q x / ‖x - ξ‖ ^ n)) (closedBall ξ ρ \ closedBall ξ σ) μ ∧ Tendsto (fun m ↦ ∫ x, u x * q x * k m ‖x - ξ‖ ∂μ) atTop (𝓝 (∫ x in closedBall ξ ρ \ closedBall ξ σ, u x * (q x / ‖x - ξ‖ ^ n) ∂μ))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
