# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.slicing-a1.slice_mass_bound-a1.cutoff_defect_bound-a1.band_limit-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-mass-bound-a1-cutoff-defect-bound-a1-band-limit-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.slicing-a1.slice_mass_bound-a1.cutoff_defect_bound-a1`
- Child key: `band_limit`
- Declaration: `Submission.slicing_mb_cdb_band_measure_tendsto`
- Exact Lean type: `∀ (P : ℕ) (μ : Measure (Eucl P)) (K : Set (Eucl P)) (f : Eucl P → ℝ) (a b : ℝ), IsClosed K → ContinuousOn f K → μ K < ∞ → Tendsto (fun j : ℕ => μ (K ∩ f ⁻¹' Ioo (a - 1 / ((j : ℝ) + 1)) (b + 1 / ((j : ℝ) + 1)))) atTop (𝓝 (μ (K ∩ f ⁻¹' Icc a b)))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
