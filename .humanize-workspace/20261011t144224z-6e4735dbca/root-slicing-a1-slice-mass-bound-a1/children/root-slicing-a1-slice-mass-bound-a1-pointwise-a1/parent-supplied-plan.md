# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.slicing-a1.slice_mass_bound-a1.pointwise-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-mass-bound-a1-pointwise-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.slicing-a1.slice_mass_bound-a1`
- Child key: `pointwise`
- Declaration: `Submission.slicing_mb_pointwise`
- Exact Lean type: `∀ (P m : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ (T : GeometricCurrentOn U (m + 1)) (μ : Measure (Eucl P)) (v : Eucl P → NVector (Eucl P) (m + 1)), IsMeasureRepresentation T μ v → (∀ K : Set (Eucl P), IsCompact K → K ⊆ U → μ K < ∞) → (∀ (x : Eucl P) (α : Covector (Eucl P) (m + 1)), |v x α| ≤ covectorEuclideanNorm α) → ∀ (f : Eucl P → ℝ) (L : ℝ≥0), LipschitzOnWith L f U → ∀ (t : ℝ) (S : GeometricCurrentOn U m), IsSlice T f t S → ∀ W : Set (Eucl P), IsOpen W → W ⊆ U → ∀ LW : ℝ≥0, (∀ᵐ x ∂(volume : Measure (Eucl P)), x ∈ W → ‖fderiv ℝ f x‖₊ ≤ LW) → S.massOn W ≤ (LW : ℝ≥0∞) * liminf (fun h : ℝ => μ (W ∩ f ⁻¹' Icc (t - h) t) / ENNReal.ofReal h) (𝓝[>] 0)`

## Sibling prerequisites

- `root.slicing-a1.slice_mass_bound-a1.cutoff-a1`
- `root.slicing-a1.slice_mass_bound-a1.cutoff_defect_bound-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
