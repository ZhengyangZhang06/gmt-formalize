# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.mass_representation-a1.vector_riesz-a1.common_density-a1.dominating_measure-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-mass-representation-a1-vec-245edb53e7/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.mass_representation-a1.vector_riesz-a1.common_density-a1`
- Child key: `dominating_measure`
- Declaration: `Submission.cmr_vr_cd_dominating_measure`
- Exact Lean type: `∀ (X : Type) [TopologicalSpace X] [MeasurableSpace X] (m : ℕ) (a b : Fin m → Measure X), (∀ i, IsFiniteMeasureOnCompacts (a i)) → (∀ i, IsFiniteMeasureOnCompacts (b i)) → ∃ μ₀ : Measure X, IsFiniteMeasureOnCompacts μ₀ ∧ (∀ i, a i ≪ μ₀) ∧ ∀ i, b i ≪ μ₀`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
