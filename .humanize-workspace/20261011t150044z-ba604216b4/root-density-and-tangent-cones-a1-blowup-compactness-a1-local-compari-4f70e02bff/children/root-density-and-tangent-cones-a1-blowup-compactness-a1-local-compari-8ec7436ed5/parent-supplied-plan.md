# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.chart_coarea-a1.piece_coarea-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-8ec7436ed5/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.chart_coarea-a1`
- Child key: `piece_coarea`
- Declaration: `Submission.dtc_bc_lc_sl_cc_piece_coarea`
- Exact Lean type: `∀ (P n : ℕ) (ψ : Euclid (n + 1) → Euclid P) (V Ω Y' : Set (Euclid (n + 1))) (F : Euclid (n + 1) → ℝ) (Θ : Euclid (n + 1) → Euclid (n + 1)) (G : Euclid P → Euclid P), IsOpen V → ContDiff ℝ 1 ψ → InjOn ψ V → (∀ y ∈ V, Injective (fderiv ℝ ψ y)) → ContDiff ℝ 1 F → IsOpen Ω → ContDiffOn ℝ 1 Θ Ω → InjOn Θ Ω → (∀ z ∈ Ω, Injective (fderiv ℝ Θ z)) → Θ '' Ω ⊆ V → (∀ z ∈ Ω, F (Θ z) = z 0) → MeasurableSet Y' → Y' ⊆ Θ '' Ω → (∀ y ∈ Y', G (ψ y) ∈ LinearMap.range (fderiv ℝ ψ y : Euclid (n + 1) →ₗ[ℝ] Euclid P) ∧ ∀ e, inner ℝ (G (ψ y)) (fderiv ℝ ψ y e) = fderiv ℝ F y e) → ∀ g : Euclid P → ℝ≥0∞, Measurable g → Measurable (fun t => ∫⁻ x in ψ '' (Y' ∩ F ⁻¹' {t}), g x ∂μHE[n]) ∧ ∫⁻ t, ∫⁻ x in ψ '' (Y' ∩ F ⁻¹' {t}), g x ∂μHE[n] = ∫⁻ x in ψ '' Y', ENNReal.ofReal ‖G x‖ * g x ∂μHE[n + 1]`

## Sibling prerequisites

- `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.chart_coarea-a1.chart_gradient-a1`
- `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.chart_coarea-a1.flat_fubini-a1`
- `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.chart_coarea-a1.slice_param-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
