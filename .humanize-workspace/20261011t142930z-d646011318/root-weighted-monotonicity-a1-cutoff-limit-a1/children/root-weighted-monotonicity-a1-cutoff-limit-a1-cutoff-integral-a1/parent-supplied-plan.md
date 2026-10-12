# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.weighted_monotonicity-a1.cutoff_limit-a1.cutoff_integral-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-weighted-monotonicity-a1-cutoff-limit-a1-cutoff-integral-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.weighted_monotonicity-a1.cutoff_limit-a1`
- Child key: `cutoff_integral`
- Declaration: `Submission.weighted_mono_cutoff_integral_tendsto`
- Exact Lean type: `∀ (n ℓ : ℕ) (μ : Measure (Ambient n ℓ)) (f : Ambient n ℓ → ℝ) (ξ : Ambient n ℓ) (t R : ℝ) (φ : ℕ → ℝ → ℝ) (ε : ℕ → ℝ), 0 < t → IntegrableOn f (closedBall ξ R) μ → Tendsto ε atTop (𝓝 0) → (∀ m, (1 + ε m) * t ≤ R) → (∀ m, Measurable (φ m)) → (∀ m s, 0 ≤ φ m s ∧ φ m s ≤ 1) → (∀ m s, s ≤ 1 → φ m s = 1) → (∀ m s, 1 + ε m ≤ s → φ m s = 0) → Tendsto (fun m ↦ ∫ x, φ m (‖x - ξ‖ / t) * f x ∂μ) atTop (𝓝 (∫ x in closedBall ξ t, f x ∂μ))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
