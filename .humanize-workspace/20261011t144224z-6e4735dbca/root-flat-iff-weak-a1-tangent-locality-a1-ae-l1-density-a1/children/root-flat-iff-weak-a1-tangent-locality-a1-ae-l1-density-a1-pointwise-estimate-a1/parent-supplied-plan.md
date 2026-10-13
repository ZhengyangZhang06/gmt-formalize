# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.flat_iff_weak-a1.tangent_locality-a1.ae_l1_density-a1.pointwise_estimate-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-flat-iff-weak-a1-tangent-locality-a1-ae-l1-density-a1-pointwise-estimate-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.flat_iff_weak-a1.tangent_locality-a1.ae_l1_density-a1`
- Child key: `pointwise_estimate`
- Declaration: `Submission.fiw_tl_ald_pointwise_estimate`
- Exact Lean type: `∀ (P n : ℕ) (M₁ M₂ : Set (Eucl P)) (θ₁ θ₂ : Eucl P → ℝ) (x : Eucl P), NullMeasurableSet M₁ (μHE[n] : Measure (Eucl P)) → NullMeasurableSet M₂ (μHE[n] : Measure (Eucl P)) → (∀ z ∈ M₁, 0 < θ₁ z) → (∀ z ∈ M₂, 0 < θ₂ z) → x ∈ M₁ ∩ M₂ → (∃ ρ : ℝ, 0 < ρ ∧ IntegrableOn θ₁ (M₁ ∩ closedBall x ρ) (μHE[n] : Measure (Eucl P)) ∧ IntegrableOn θ₂ (M₂ ∩ closedBall x ρ) (μHE[n] : Measure (Eucl P))) → Tendsto (fun s : ℝ => (∫⁻ z in M₁ ∩ closedBall x s, ENNReal.ofReal (θ₁ z) * ‖(M₁ ∩ M₂).indicator (fun w => θ₂ w / θ₁ w) z - θ₂ x / θ₁ x‖ₑ ∂(μHE[n] : Measure (Eucl P))) / (∫⁻ z in M₁ ∩ closedBall x s, ENNReal.ofReal (θ₁ z) ∂(μHE[n] : Measure (Eucl P)))) (𝓝[>] 0) (𝓝 0) → Tendsto (fun s : ℝ => (∫⁻ z in M₁ ∩ M₂ ∩ closedBall x s, ENNReal.ofReal (θ₂ z) ∂(μHE[n] : Measure (Eucl P))) / (∫⁻ z in M₂ ∩ closedBall x s, ENNReal.ofReal (θ₂ z) ∂(μHE[n] : Measure (Eucl P)))) (𝓝[>] 0) (𝓝 1) → ∀ ε : ℝ, 0 < ε → ∀ᶠ s in 𝓝[>] (0 : ℝ), ∫⁻ z in closedBall x s, ‖M₂.indicator θ₂ z - θ₂ x / θ₁ x * M₁.indicator θ₁ z‖ₑ ∂(μHE[n] : Measure (Eucl P)) ≤ ENNReal.ofReal ε * ∫⁻ z in M₁ ∩ closedBall x s, ENNReal.ofReal (θ₁ z) ∂(μHE[n] : Measure (Eucl P))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
