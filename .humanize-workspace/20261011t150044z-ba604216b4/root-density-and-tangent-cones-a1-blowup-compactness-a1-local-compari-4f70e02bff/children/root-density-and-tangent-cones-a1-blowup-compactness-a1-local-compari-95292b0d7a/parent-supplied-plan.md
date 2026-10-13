# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.chart_coarea-a1.regular_coarea-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-95292b0d7a/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.chart_coarea-a1`
- Child key: `regular_coarea`
- Declaration: `Submission.dtc_bc_lc_sl_cc_regular_coarea`
- Exact Lean type: `∀ (P n : ℕ) (ψ : Euclid (n + 1) → Euclid P) (V Y' : Set (Euclid (n + 1))) (F : Euclid (n + 1) → ℝ) (G : Euclid P → Euclid P), IsOpen V → ContDiff ℝ 1 ψ → InjOn ψ V → (∀ y ∈ V, Injective (fderiv ℝ ψ y)) → ContDiff ℝ 1 F → MeasurableSet Y' → Y' ⊆ V → (∀ y ∈ Y', fderiv ℝ F y ≠ 0) → (∀ y ∈ Y', G (ψ y) ∈ LinearMap.range (fderiv ℝ ψ y : Euclid (n + 1) →ₗ[ℝ] Euclid P) ∧ ∀ e, inner ℝ (G (ψ y)) (fderiv ℝ ψ y e) = fderiv ℝ F y e) → ∀ g : Euclid P → ℝ≥0∞, Measurable g → Measurable (fun t => ∫⁻ x in ψ '' (Y' ∩ F ⁻¹' {t}), g x ∂μHE[n]) ∧ ∫⁻ t, ∫⁻ x in ψ '' (Y' ∩ F ⁻¹' {t}), g x ∂μHE[n] = ∫⁻ x in ψ '' Y', ENNReal.ofReal ‖G x‖ * g x ∂μHE[n + 1]`

## Sibling prerequisites

- `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.chart_coarea-a1.flattening_atlas-a1`
- `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.chart_coarea-a1.piece_coarea-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
