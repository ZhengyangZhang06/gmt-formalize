# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.mass_representation-a1.vector_riesz-a1.common_density-a1.density_representation-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-mass-representation-a1-vec-d113441fe0/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.mass_representation-a1.vector_riesz-a1.common_density-a1`
- Child key: `density_representation`
- Declaration: `Submission.cmr_vr_cd_density_representation`
- Exact Lean type: `∀ (X : Type) [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] (μ₀ ξ : Measure X), IsFiniteMeasureOnCompacts μ₀ → IsFiniteMeasureOnCompacts ξ → ξ ≪ μ₀ → ∃ g : X → ℝ, Measurable g ∧ (∀ K : Set X, IsCompact K → IntegrableOn g K μ₀) ∧ ∀ f : CompactlySupportedContinuousMap X ℝ, Integrable (fun x => f x * g x) μ₀ ∧ ∫ x, f x ∂ξ = ∫ x, f x * g x ∂μ₀`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
