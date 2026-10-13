# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.monotonicity-a1.support_density_lower_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-monotonicity-a1-support-density-l-69839965cf/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.monotonicity-a1`
- Child key: `support_density_lower_bound`
- Declaration: `Submission.dimred_mono_support_density_ge_one_of_usc`
- Exact Lean type: `∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (μ : Measure (Euclid P)) (Θ : Euclid P → ℝ), IsOpen U → (∀ W : Set (Euclid P), IsOpen W → W ⊆ U → T.massOn W = μ W) → (∀ x ∈ T.support, ∀ ε : ℝ, 0 < ε → μ (ball x ε) ≠ 0) → (∀ᵐ x ∂μ, ∀ θ : ℝ, Tendsto (fun ρ : ℝ => μ (ball x ρ) / (unitBallVolume n * ENNReal.ofReal (ρ ^ n))) (𝓝[>] 0) (𝓝 (ENNReal.ofReal θ)) → 1 ≤ θ) → (∀ y ∈ U, HasMassDensity T y (Θ y)) → UpperSemicontinuousOn Θ U → ∀ y ∈ T.support, ∀ θ : ℝ, HasMassDensity T y θ → 1 ≤ θ`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
