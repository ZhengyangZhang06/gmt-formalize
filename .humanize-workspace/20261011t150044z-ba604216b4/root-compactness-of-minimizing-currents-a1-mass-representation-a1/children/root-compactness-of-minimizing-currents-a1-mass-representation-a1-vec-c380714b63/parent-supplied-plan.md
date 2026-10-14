# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.mass_representation-a1.vector_riesz-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-mass-representation-a1-vec-c380714b63/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.mass_representation-a1`
- Child key: `vector_riesz`
- Declaration: `Submission.cmr_vector_riesz_representation`
- Exact Lean type: `∀ (X : Type) [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] (d : ℕ) (L : CompactlySupportedContinuousMap X (EuclideanSpace ℝ (Fin d)) →ₗ[ℝ] ℝ), (∀ K : Set X, IsCompact K → ∃ M : ℝ, ∀ g : CompactlySupportedContinuousMap X (EuclideanSpace ℝ (Fin d)), tsupport g ⊆ K → (∀ x, ‖g x‖ ≤ 1) → |L g| ≤ M) → ∃ (μ₀ : Measure X) (ν : X → EuclideanSpace ℝ (Fin d)), IsFiniteMeasureOnCompacts μ₀ ∧ Measurable ν ∧ (∀ K : Set X, IsCompact K → IntegrableOn ν K μ₀) ∧ ∀ g : CompactlySupportedContinuousMap X (EuclideanSpace ℝ (Fin d)), L g = ∫ x, inner ℝ (g x) (ν x) ∂μ₀`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
