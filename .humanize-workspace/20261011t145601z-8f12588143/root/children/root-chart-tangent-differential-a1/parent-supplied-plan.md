# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.chart_tangent_differential-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-chart-tangent-differential-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root`
- Child key: `chart_tangent_differential`
- Declaration: `Submission.chart_approx_tangent_and_differential`
- Exact Lean type: `∀ (n ℓ p : ℕ) (M U : Set (Rn (n + ℓ))) (θ : Rn (n + ℓ) → ℝ) (f : Rn (n + ℓ) → Rn p) (V : Set (Rn n)) (ψ : Rn n → Rn (n + ℓ)), NullMeasurableSet M μHE[n] → IsPositiveLocallyIntegrableWeight n M θ → IsOpen U → M ⊆ U → LocallyLipschitzOn U f → IsOpen V → ContDiffOn ℝ 1 ψ V → (∀ u ∈ V, Function.Injective (fderiv ℝ ψ u)) → ∀ᵐ u ∂(volume : Measure (Rn n)), u ∈ V → ψ u ∈ M → HasWeightedApproximateTangentSpaceAt n M θ (ψ u) (LinearMap.range (fderiv ℝ ψ u).toLinearMap) ∧ DifferentiableAt ℝ (f ∘ ψ) u ∧ ∀ w : Rn n, HasLineDerivAt ℝ f (fderiv ℝ (f ∘ ψ) u w) (ψ u) (fderiv ℝ ψ u w)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
