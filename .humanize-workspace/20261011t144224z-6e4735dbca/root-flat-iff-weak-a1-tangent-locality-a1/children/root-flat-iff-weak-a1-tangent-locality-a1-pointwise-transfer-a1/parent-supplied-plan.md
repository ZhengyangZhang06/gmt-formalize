# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.flat_iff_weak-a1.tangent_locality-a1.pointwise_transfer-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-flat-iff-weak-a1-tangent-locality-a1-pointwise-transfer-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.flat_iff_weak-a1.tangent_locality-a1`
- Child key: `pointwise_transfer`
- Declaration: `Submission.fiw_tl_transfer`
- Exact Lean type: `∀ (P n : ℕ) (M₁ M₂ : Set (Eucl P)) (θ₁ θ₂ : Eucl P → ℝ) (x : Eucl P) (c ρ : ℝ), 0 < ρ → NullMeasurableSet M₁ (μHE[n] : Measure (Eucl P)) → NullMeasurableSet M₂ (μHE[n] : Measure (Eucl P)) → (∀ y ∈ M₁, 0 ≤ θ₁ y) → IntegrableOn θ₁ (M₁ ∩ closedBall x ρ) (μHE[n] : Measure (Eucl P)) → IntegrableOn θ₂ (M₂ ∩ closedBall x ρ) (μHE[n] : Measure (Eucl P)) → θ₂ x = c * θ₁ x → (∀ ε : ℝ, 0 < ε → ∀ᶠ s in 𝓝[>] (0 : ℝ), ∫⁻ z in closedBall x s, ‖M₂.indicator θ₂ z - c * M₁.indicator θ₁ z‖ₑ ∂(μHE[n] : Measure (Eucl P)) ≤ ENNReal.ofReal ε * ∫⁻ z in M₁ ∩ closedBall x s, ENNReal.ofReal (θ₁ z) ∂(μHE[n] : Measure (Eucl P))) → ∀ Q : Submodule ℝ (Eucl P), HasWeightedApproximateTangentSpaceAt n M₁ θ₁ x Q → HasWeightedApproximateTangentSpaceAt n M₂ θ₂ x Q`

## Sibling prerequisites

- `root.flat_iff_weak-a1.tangent_locality-a1.blowup_change_of_variables-a1`
- `root.flat_iff_weak-a1.tangent_locality-a1.growth_bound-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
