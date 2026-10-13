# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.slicing-a1.mass_representation-a1.riesz_borel-a1.borel_riesz-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-mass-representation-a1-riesz-borel-a1-borel-riesz-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.slicing-a1.mass_representation-a1.riesz_borel-a1`
- Child key: `borel_riesz`
- Declaration: `Submission.smr_rb_borel_riesz_sigma_compact`
- Exact Lean type: `∀ (Y : Type) [TopologicalSpace Y] [T2Space Y] [LocallyCompactSpace Y] [SigmaCompactSpace Y] [MeasurableSpace Y] [BorelSpace Y] (N : ℕ) (L : CompactlySupportedContinuousMap Y (EuclideanSpace ℝ (Fin N)) →ₗ[ℝ] ℝ), (∀ K : Set Y, IsCompact K → ∃ B : ℝ, ∀ g : CompactlySupportedContinuousMap Y (EuclideanSpace ℝ (Fin N)), (∀ y, ‖g y‖ ≤ 1) → tsupport g ⊆ K → L g ≤ B) → ∃ (m : Measure Y) (ν : Y → EuclideanSpace ℝ (Fin N)), (∀ K : Set Y, IsCompact K → m K < ∞) ∧ Measurable ν ∧ (∀ y, ‖ν y‖ ≤ 1) ∧ (∀ᵐ y ∂m, ‖ν y‖ = 1) ∧ ∀ g : CompactlySupportedContinuousMap Y (EuclideanSpace ℝ (Fin N)), L g = ∫ y, inner ℝ (g y) (ν y) ∂m`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
