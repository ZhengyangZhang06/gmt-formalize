# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.integrality_weak_limits-a1.im_closure-a1.tangent_overlap-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-im-closure-a1-tangent-overlap-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.integrality_weak_limits-a1.im_closure-a1`
- Child key: `tangent_overlap`
- Declaration: `Submission.iwl_imc_tangent_overlap`
- Exact Lean type: `∀ (P k : ℕ), (∀ (M M' : Set (Eucl P)) (θ θ' : Eucl P → ℝ) (x : Eucl P), NullMeasurableSet M (μHE[k] : Measure (Eucl P)) → NullMeasurableSet M' (μHE[k] : Measure (Eucl P)) → θ x = θ' x → (∃ ρ : ℝ, 0 < ρ ∧ IntegrableOn θ (M ∩ closedBall x ρ) (μHE[k] : Measure (Eucl P)) ∧ IntegrableOn θ' (M' ∩ closedBall x ρ) (μHE[k] : Measure (Eucl P))) → (∀ R : ℝ, 0 < R → Tendsto (fun r : ℝ => ENNReal.ofReal ((r ^ k)⁻¹) * ∫⁻ z in closedBall x (R * r), ‖M.indicator θ z - M'.indicator θ' z‖ₑ ∂(μHE[k] : Measure (Eucl P))) (𝓝[>] 0) (𝓝 0)) → ∀ Q : Submodule ℝ (Eucl P), HasWeightedApproximateTangentSpaceAt k M θ x Q ↔ HasWeightedApproximateTangentSpaceAt k M' θ' x Q) → ∀ U : Set (Eucl P), IsOpen U → ∀ (M₁ M₂ : Set (Eucl P)) (θ₁ θ₂ : Eucl P → ℝ), M₁ ⊆ U → M₂ ⊆ U → NullMeasurableSet M₁ (μHE[k] : Measure (Eucl P)) → NullMeasurableSet M₂ (μHE[k] : Measure (Eucl P)) → (∀ x ∈ M₁, 1 ≤ θ₁ x) → (∀ x ∈ M₂, 1 ≤ θ₂ x) → (∀ K : Set (Eucl P), IsCompact K → K ⊆ U → IntegrableOn θ₁ (M₁ ∩ K) (μHE[k] : Measure (Eucl P))) → (∀ K : Set (Eucl P), IsCompact K → K ⊆ U → IntegrableOn θ₂ (M₂ ∩ K) (μHE[k] : Measure (Eucl P))) → ∀ᵐ x ∂((μHE[k] : Measure (Eucl P)).restrict (M₁ ∩ M₂)), ∀ Q : Submodule ℝ (Eucl P), HasWeightedApproximateTangentSpaceAt k M₁ θ₁ x Q → HasWeightedApproximateTangentSpaceAt k M₂ θ₂ x Q`

## Sibling prerequisites

- `root.integrality_weak_limits-a1.im_closure-a1.density_zero_off_set-a1`
- `root.integrality_weak_limits-a1.im_closure-a1.lebesgue_points-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
