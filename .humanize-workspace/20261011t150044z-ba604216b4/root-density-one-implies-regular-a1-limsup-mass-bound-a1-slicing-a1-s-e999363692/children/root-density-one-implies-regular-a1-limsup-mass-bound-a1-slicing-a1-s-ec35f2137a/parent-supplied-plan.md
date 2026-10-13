# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.piece_coarea-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-slicing-a1-s-ec35f2137a/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1`
- Child key: `piece_coarea`
- Declaration: `Submission.dor_lmbsf_piece_coarea`
- Exact Lean type: `∀ (P n : ℕ) (V C Y : Set (Euclid (n + 1))) (ψ : Euclid (n + 1) → Euclid P) (F : Euclid (n + 1) → ℝ) (f : Euclid P → ℝ) (G : Euclid P → Euclid P), IsOpen V → ContDiffOn ℝ 1 ψ V → InjOn ψ V → (∀ y ∈ V, Injective (fderiv ℝ ψ y)) → IsCompact C → C ⊆ V → MeasurableSet Y → Y ⊆ C → ContDiff ℝ 1 F → (∀ y ∈ Y, f (ψ y) = F y) → (∀ y ∈ Y, G (ψ y) ∈ LinearMap.range (fderiv ℝ ψ y : Euclid (n + 1) →ₗ[ℝ] Euclid P) ∧ ∀ e : Euclid (n + 1), inner ℝ (G (ψ y)) (fderiv ℝ ψ y e) = fderiv ℝ F y e) → Measurable G → ∀ φ : Euclid P → ℝ≥0∞, Measurable φ → AEMeasurable (fun t => ∫⁻ x in ψ '' Y ∩ {x | G x ≠ 0} ∩ f ⁻¹' {t}, φ x ∂μHE[n]) ∧ ∫⁻ t, (∫⁻ x in ψ '' Y ∩ {x | G x ≠ 0} ∩ f ⁻¹' {t}, φ x ∂μHE[n]) = ∫⁻ x in ψ '' Y, ‖G x‖ₑ * φ x ∂μHE[n + 1]`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
