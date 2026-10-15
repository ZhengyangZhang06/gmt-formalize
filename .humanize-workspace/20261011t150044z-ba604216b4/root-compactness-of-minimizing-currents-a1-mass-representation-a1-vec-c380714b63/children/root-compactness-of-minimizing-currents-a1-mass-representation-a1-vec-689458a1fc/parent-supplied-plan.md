# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.mass_representation-a1.vector_riesz-a1.jordan_decomposition-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-mass-representation-a1-vec-689458a1fc/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.mass_representation-a1.vector_riesz-a1`
- Child key: `jordan_decomposition`
- Declaration: `Submission.cmr_vr_jordan_decomposition`
- Exact Lean type: `∀ (X : Type) [TopologicalSpace X] (Λ : CompactlySupportedContinuousMap X ℝ →ₗ[ℝ] ℝ), (∀ K : Set X, IsCompact K → ∃ M : ℝ, ∀ f : CompactlySupportedContinuousMap X ℝ, tsupport f ⊆ K → (∀ x, |f x| ≤ 1) → |Λ f| ≤ M) → ∃ Λ₁ Λ₂ : CompactlySupportedContinuousMap X ℝ →ₚ[ℝ] ℝ, ∀ f : CompactlySupportedContinuousMap X ℝ, Λ f = Λ₁ f - Λ₂ f`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
