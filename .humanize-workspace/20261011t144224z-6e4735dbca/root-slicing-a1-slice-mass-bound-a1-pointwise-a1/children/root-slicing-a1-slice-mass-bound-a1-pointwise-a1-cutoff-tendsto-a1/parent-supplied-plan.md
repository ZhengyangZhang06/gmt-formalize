# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.slicing-a1.slice_mass_bound-a1.pointwise-a1.cutoff_tendsto-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-mass-bound-a1-pointwise-a1-cutoff-tendsto-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.slicing-a1.slice_mass_bound-a1.pointwise-a1`
- Child key: `cutoff_tendsto`
- Declaration: `Submission.slicing_mb_pointwise_cutoff_tendsto`
- Exact Lean type: `∀ (P : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ (f : Eucl P → ℝ) (L : ℝ≥0), LipschitzOnWith L f U → ∀ (ν : Measure (Eucl P)) (F : Eucl P → ℝ), Integrable F ν → (∀ x, x ∉ U → F x = 0) → ∀ (t : ℝ) (χ : ℝ → ℝ → ℝ), (∀ h : ℝ, 0 < h → Measurable (χ h)) → (∀ h s : ℝ, 0 < h → |χ h s| ≤ 1) → (∀ h s : ℝ, 0 < h → s ≤ t - h → χ h s = 1) → (∀ h s : ℝ, 0 < h → t ≤ s → χ h s = 0) → Tendsto (fun h : ℝ => ∫ x, χ h (f x) * F x ∂ν) (𝓝[>] 0) (𝓝 (∫ x in {x | x ∈ U ∧ f x < t}, F x ∂ν))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
