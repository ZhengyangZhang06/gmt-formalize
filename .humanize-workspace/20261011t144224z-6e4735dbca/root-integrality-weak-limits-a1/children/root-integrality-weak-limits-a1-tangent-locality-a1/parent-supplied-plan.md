# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.integrality_weak_limits-a1.tangent_locality-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-tangent-locality-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.integrality_weak_limits-a1`
- Child key: `tangent_locality`
- Declaration: `Submission.iwl_weighted_tangent_locality`
- Exact Lean type: `∀ (P n : ℕ) (M M' : Set (Eucl P)) (θ θ' : Eucl P → ℝ) (x : Eucl P), NullMeasurableSet M (μHE[n] : Measure (Eucl P)) → NullMeasurableSet M' (μHE[n] : Measure (Eucl P)) → θ x = θ' x → (∃ ρ : ℝ, 0 < ρ ∧ IntegrableOn θ (M ∩ closedBall x ρ) (μHE[n] : Measure (Eucl P)) ∧ IntegrableOn θ' (M' ∩ closedBall x ρ) (μHE[n] : Measure (Eucl P))) → (∀ R : ℝ, 0 < R → Tendsto (fun r : ℝ => ENNReal.ofReal ((r ^ n)⁻¹) * ∫⁻ z in closedBall x (R * r), ‖M.indicator θ z - M'.indicator θ' z‖ₑ ∂(μHE[n] : Measure (Eucl P))) (𝓝[>] 0) (𝓝 0)) → ∀ Q : Submodule ℝ (Eucl P), HasWeightedApproximateTangentSpaceAt n M θ x Q ↔ HasWeightedApproximateTangentSpaceAt n M' θ' x Q`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
