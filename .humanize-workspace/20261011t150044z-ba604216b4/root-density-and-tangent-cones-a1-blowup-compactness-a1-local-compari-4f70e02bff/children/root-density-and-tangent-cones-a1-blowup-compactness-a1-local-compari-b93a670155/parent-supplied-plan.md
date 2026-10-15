# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.chart_coarea-a1.critical_null-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-b93a670155/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.chart_coarea-a1`
- Child key: `critical_null`
- Declaration: `Submission.dtc_bc_lc_sl_cc_critical_null`
- Exact Lean type: `∀ (n : ℕ) (C : NNReal), (∀ (A : Set (Euclid (n + 1))) (f : Euclid (n + 1) → ℝ) (L : NNReal), LipschitzOnWith L f A → ∃ φ : ℝ → ℝ≥0∞, Measurable φ ∧ (∀ t, μHE[n] (A ∩ f ⁻¹' {t}) ≤ φ t) ∧ ∫⁻ t, φ t ≤ (C : ℝ≥0∞) * (L : ℝ≥0∞) * μHE[n + 1] A) → ∀ (F : Euclid (n + 1) → ℝ) (Z : Set (Euclid (n + 1))), ContDiff ℝ 1 F → (∀ y ∈ Z, fderiv ℝ F y = 0) → ∀ᵐ t, μHE[n] (Z ∩ F ⁻¹' {t}) = 0`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
