# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.chart_coarea-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-4f70e02bff/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1`
- Child key: `chart_coarea`
- Declaration: `Submission.dtc_bc_lc_sl_chart_coarea`
- Exact Lean type: `∀ (P n : ℕ) (ψ : Euclid (n + 1) → Euclid P) (V Y : Set (Euclid (n + 1))) (F : Euclid (n + 1) → ℝ) (G : Euclid P → Euclid P), IsOpen V → ContDiff ℝ 1 ψ → InjOn ψ V → (∀ y ∈ V, Injective (fderiv ℝ ψ y)) → ContDiff ℝ 1 F → MeasurableSet Y → IsCompact (closure Y) → closure Y ⊆ V → (∀ y ∈ Y, G (ψ y) ∈ LinearMap.range (fderiv ℝ ψ y : Euclid (n + 1) →ₗ[ℝ] Euclid P) ∧ ∀ e, inner ℝ (G (ψ y)) (fderiv ℝ ψ y e) = fderiv ℝ F y e) → (∀ g : Euclid P → ℝ≥0∞, Measurable g → AEMeasurable (fun t => ∫⁻ x in ψ '' (Y ∩ F ⁻¹' {t}), g x ∂μHE[n]) ∧ ∫⁻ t, ∫⁻ x in ψ '' (Y ∩ F ⁻¹' {t}), g x ∂μHE[n] = ∫⁻ x in ψ '' Y, ENNReal.ofReal ‖G x‖ * g x ∂μHE[n + 1]) ∧ ∀ᵐ t, CountablyRectifiable n (ψ '' (Y ∩ F ⁻¹' {t})) ∧ ∀ᵐ x ∂(μHE[n].restrict (ψ '' (Y ∩ F ⁻¹' {t}))), G x ≠ 0 ∧ ∀ y ∈ Y, ψ y = x → HasApproximateTangentSpaceAt n (ψ '' (Y ∩ F ⁻¹' {t})) x (LinearMap.range (fderiv ℝ ψ y : Euclid (n + 1) →ₗ[ℝ] Euclid P) ⊓ (ℝ ∙ G x)ᗮ)`

## Sibling prerequisites

- `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.eilenberg-a1`
- `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.c1_tangent-a1`
- `root.compactness_of_minimizing_currents-a1.im_calculus-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
