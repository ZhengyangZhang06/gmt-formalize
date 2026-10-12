# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.flat_iff_weak-a1.tangent_locality-a1.pointwise_transfer-a1.weighted_diff_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-flat-iff-weak-a1-tangent-locality-a1-pointwise-transfer-a1-weigh-bf77e528cf/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.flat_iff_weak-a1.tangent_locality-a1.pointwise_transfer-a1`
- Child key: `weighted_diff_bound`
- Declaration: `Submission.fiw_tl_tr_weighted_diff_bound`
- Exact Lean type: `∀ (P n : ℕ) (M₁ M₂ : Set (Eucl P)) (θ₁ θ₂ φ : Eucl P → ℝ) (x : Eucl P) (c ρ s K : ℝ), NullMeasurableSet M₁ (μHE[n] : Measure (Eucl P)) → NullMeasurableSet M₂ (μHE[n] : Measure (Eucl P)) → IntegrableOn θ₁ (M₁ ∩ closedBall x ρ) (μHE[n] : Measure (Eucl P)) → IntegrableOn θ₂ (M₂ ∩ closedBall x ρ) (μHE[n] : Measure (Eucl P)) → Continuous φ → (∀ z, ‖φ z‖ ≤ K) → (∀ z, z ∉ closedBall x s → φ z = 0) → s ≤ ρ → ‖(∫ z in M₂, φ z * θ₂ z ∂(μHE[n] : Measure (Eucl P))) - c * ∫ z in M₁, φ z * θ₁ z ∂(μHE[n] : Measure (Eucl P))‖ₑ ≤ ENNReal.ofReal K * ∫⁻ z in closedBall x s, ‖M₂.indicator θ₂ z - c * M₁.indicator θ₁ z‖ₑ ∂(μHE[n] : Measure (Eucl P))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
