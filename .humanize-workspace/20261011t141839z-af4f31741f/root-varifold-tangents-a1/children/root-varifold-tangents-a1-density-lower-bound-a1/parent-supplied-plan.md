# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.varifold_tangents-a1.density_lower_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-varifold-tangents-a1-density-lower-bound-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.varifold_tangents-a1`
- Child key: `density_lower_bound`
- Declaration: `Submission.varifold_tangents_density_lower_bound`
- Exact Lean type: `DensitySemicontinuity → ∀ (N n : ℕ) (U : Set (Euclidean N)) (V : Varifold N n U) (x : Euclidean N) (τ : ℝ), V.HasLocallyBoundedFirstVariation → x ∈ U → 0 < τ → Tendsto (fun ρ : ℝ ↦ ENNReal.ofReal ρ * variationMeasure V (closedBall x ρ) / ENNReal.ofReal ρ ^ n) (𝓝[>] 0) (𝓝 0) → Tendsto (fun ρ : ℝ ↦ V.weight {y | y ∈ closedBall x ρ ∧ ¬ ∃ θ : ℝ≥0∞, HasDensity n V.weight y θ ∧ ENNReal.ofReal τ ≤ θ} / ENNReal.ofReal ρ ^ n) (𝓝[>] 0) (𝓝 0) → ∀ C : Varifold N n (univ : Set (Euclidean N)), IsVarifoldTangent V x C → ∀ᵐ y ∂C.weight, ∃ θ : ℝ≥0∞, HasDensity n C.weight y θ ∧ ENNReal.ofReal τ ≤ θ`

## Sibling prerequisites

- `root.varifold_tangents-a1.rescaled_divergence_bound-a1`
- `root.varifold_tangents-a1.restrict_radon_converges-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
