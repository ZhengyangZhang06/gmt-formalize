# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.slicing-a1.slice_mass_bound-a1.cutoff_defect_bound-a1.grad_lintegral-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-mass-bound-a1-cutoff-defect-bound-a1-grad-lintegral-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.slicing-a1.slice_mass_bound-a1.cutoff_defect_bound-a1`
- Child key: `grad_lintegral`
- Declaration: `Submission.slicing_mb_cdb_grad_lintegral_le`
- Exact Lean type: `∀ (P m : ℕ) (μ : Measure (Eucl P)) (ω : DifferentialForm (Eucl P) m) (f g : Eucl P → ℝ) (LW : ℝ≥0) (χ : ℝ → ℝ) (t h c δ : ℝ), (∀ x, covectorEuclideanNorm (ω x) ≤ 1) → Differentiable ℝ g → Differentiable ℝ χ → (∀ x ∈ tsupport ω, |g x - f x| ≤ δ) → (∀ x ∈ tsupport ω, ‖fderiv ℝ g x‖₊ ≤ LW) → (∀ s, |deriv χ s| ≤ c) → (∀ s, s ∉ Ioo (t - h) t → deriv χ s = 0) → ∫⁻ x, (‖fderiv ℝ (fun y => χ (g y)) x‖₊ : ℝ≥0∞) * ENNReal.ofReal (covectorEuclideanNorm (ω x)) ∂μ ≤ ENNReal.ofReal c * (LW : ℝ≥0∞) * μ (tsupport ω ∩ f ⁻¹' Ioo (t - h - δ) (t + δ))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
