# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.lower_density-a1.covering-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-77789fb32b/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.lower_density-a1`
- Child key: `covering`
- Declaration: `Submission.cbrld_vitali_setIntegral_le`
- Exact Lean type: `∀ (P : ℕ) (μ : Measure (Euclid P)) (g : Euclid P → ℝ) (θ : ℝ) (E W : Set (Euclid P)), (∀ K : Set (Euclid P), IsCompact K → μ K < ∞) → AEStronglyMeasurable g μ → (∀ᵐ x ∂μ, |g x| ≤ 1) → θ ≤ 1 → IsOpen W → E ⊆ W → μ W < ∞ → (∀ x ∈ E, ∀ δ : ℝ, 0 < δ → ∃ ρ : ℝ, 0 < ρ ∧ ρ < δ ∧ ∫ y in closedBall x ρ, g y ∂μ ≤ θ * (μ (closedBall x ρ)).toReal) → ∫ y in W, g y ∂μ ≤ (μ W).toReal - (1 - θ) * (μ E).toReal`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
