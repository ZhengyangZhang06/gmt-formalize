# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.piece_coarea-a1.chart_patch-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-slicing-a1-s-a1a1a3825b/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.piece_coarea-a1`
- Child key: `chart_patch`
- Declaration: `Submission.dor_lmbsf_pc_chart_patch_coarea`
- Exact Lean type: `∀ (P n : ℕ) (V B Z : Set (Euclid (n + 1))) (ψ : Euclid (n + 1) → Euclid P) (F : Euclid (n + 1) → ℝ) (Ψ : Euclid (n + 1) → Euclid (n + 1)) (G : Euclid P → Euclid P), IsOpen V → ContDiffOn ℝ 1 ψ V → InjOn ψ V → (∀ y ∈ V, Injective (fderiv ℝ ψ y)) → ContDiff ℝ 1 F → IsOpen B → ContDiffOn ℝ 1 Ψ B → InjOn Ψ B → (∀ w ∈ B, Bijective (fderiv ℝ Ψ w)) → (∀ w ∈ B, F (Ψ w) = w 0) → MeasurableSet Z → Z ⊆ V → Z ⊆ Ψ '' B → (∀ y ∈ Z, G (ψ y) ∈ LinearMap.range (fderiv ℝ ψ y : Euclid (n + 1) →ₗ[ℝ] Euclid P) ∧ ∀ e : Euclid (n + 1), inner ℝ (G (ψ y)) (fderiv ℝ ψ y e) = fderiv ℝ F y e) → ∀ φ : Euclid P → ℝ≥0∞, Measurable φ → AEMeasurable (fun t : ℝ => ∫⁻ x in ψ '' (Z ∩ F ⁻¹' {t}), φ x ∂μHE[n]) ∧ ∫⁻ t : ℝ, (∫⁻ x in ψ '' (Z ∩ F ⁻¹' {t}), φ x ∂μHE[n]) = ∫⁻ x in ψ '' Z, ‖G x‖ₑ * φ x ∂μHE[n + 1]`

## Sibling prerequisites

- `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.piece_coarea-a1.param_coarea-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
