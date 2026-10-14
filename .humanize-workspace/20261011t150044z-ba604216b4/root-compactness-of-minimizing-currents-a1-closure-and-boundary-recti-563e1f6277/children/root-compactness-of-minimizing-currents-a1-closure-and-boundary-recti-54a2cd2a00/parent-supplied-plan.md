# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.rectifiable-a1.uniform_density-a1.ae_lusin-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-54a2cd2a00/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.rectifiable-a1.uniform_density-a1`
- Child key: `ae_lusin`
- Declaration: `Submission.cbrr_ud_lusin_of_aestronglyMeasurable`
- Exact Lean type: `∀ (P : ℕ) {Y : Type} [TopologicalSpace Y] [TopologicalSpace.PseudoMetrizableSpace Y] [SecondCountableTopology Y] (μ : Measure (Euclid P)) (A : Set (Euclid P)) (f : Euclid P → Y) (p : Euclid P → Prop), MeasurableSet A → μ A ≠ ∞ → AEStronglyMeasurable f (μ.restrict A) → (∀ᵐ x ∂(μ.restrict A), p x) → ∀ η : ℝ≥0∞, η ≠ 0 → ∃ K : Set (Euclid P), IsCompact K ∧ K ⊆ A ∧ μ (A \ K) < η ∧ (∀ x ∈ K, p x) ∧ ContinuousOn f K`

## Sibling prerequisites

- `root.density_one_implies_regular-a1.imrep_mass_and_support-a1.lusin_covector-a1.lusin_measurable-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
