# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.slicing-a1.slice_mass_bound-a1.cutoff_defect_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-mass-bound-a1-cutoff-defect-bound-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.slicing-a1.slice_mass_bound-a1`
- Child key: `cutoff_defect_bound`
- Declaration: `Submission.slicing_mb_cutoff_defect_bound`
- Exact Lean type: `∀ (P m : ℕ) (U : Set (Eucl P)) (T : GeometricCurrentOn U (m + 1)) (μ : Measure (Eucl P)) (v : Eucl P → NVector (Eucl P) (m + 1)), IsMeasureRepresentation T μ v → (∀ K : Set (Eucl P), IsCompact K → K ⊆ U → μ K < ∞) → (∀ (x : Eucl P) (α : Covector (Eucl P) (m + 1)), |v x α| ≤ covectorEuclideanNorm α) → ∀ (μ₁ : Measure (Eucl P)) (v₁ : Eucl P → NVector (Eucl P) (m + 1)), IsMeasureRepresentation T μ₁ v₁ → ∀ (μ₂ : Measure (Eucl P)) (v₂ : Eucl P → NVector (Eucl P) m), IsMeasureRepresentation T.boundary μ₂ v₂ → ∀ (f : Eucl P → ℝ) (L : ℝ≥0), LipschitzOnWith L f U → ∀ W : Set (Eucl P), IsOpen W → W ⊆ U → ∀ LW : ℝ≥0, (∀ᵐ x ∂(volume : Measure (Eucl P)), x ∈ W → ‖fderiv ℝ f x‖₊ ≤ LW) → ∀ ω : TestFormOn U m, tsupport (ω : DifferentialForm (Eucl P) m) ⊆ W → (∀ x, covectorEuclideanNorm ((ω : DifferentialForm (Eucl P) m) x) ≤ 1) → ∀ (χ : ℝ → ℝ) (t h c : ℝ), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ → (∀ s, |χ s| ≤ 1) → (∀ s, |deriv χ s| ≤ c) → (∀ s, s ∉ Ioo (t - h) t → deriv χ s = 0) → ENNReal.ofReal |∫ x, χ (f x) * v₂ x ((ω : DifferentialForm (Eucl P) m) x) ∂μ₂ - ∫ x, χ (f x) * v₁ x (exteriorDerivative (ω : DifferentialForm (Eucl P) m) x) ∂μ₁| ≤ ENNReal.ofReal c * (LW : ℝ≥0∞) * μ (tsupport (ω : DifferentialForm (Eucl P) m) ∩ f ⁻¹' Icc (t - h) t)`

## Sibling prerequisites

- `root.slicing-a1.slice_mass_bound-a1.smooth_approx-a1`
- `root.slicing-a1.slice_mass_bound-a1.leibniz_bound-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
