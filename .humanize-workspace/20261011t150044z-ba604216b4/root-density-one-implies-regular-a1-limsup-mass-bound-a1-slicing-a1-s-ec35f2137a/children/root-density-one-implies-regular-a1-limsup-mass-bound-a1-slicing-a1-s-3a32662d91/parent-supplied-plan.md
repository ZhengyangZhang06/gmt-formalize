# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.piece_coarea-a1.coarea_glue-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-slicing-a1-s-3a32662d91/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.piece_coarea-a1`
- Child key: `coarea_glue`
- Declaration: `Submission.dor_lmbsf_pc_coarea_glue`
- Exact Lean type: `∀ (P n : ℕ) (Z : Set (Euclid (n + 1))) (Zs : ℕ → Set (Euclid (n + 1))) (ψ : Euclid (n + 1) → Euclid P) (F : Euclid (n + 1) → ℝ) (φ g : Euclid P → ℝ≥0∞), ContinuousOn ψ Z → InjOn ψ Z → Measurable F → (∀ q, MeasurableSet (Zs q)) → Pairwise (fun p q => Disjoint (Zs p) (Zs q)) → (⋃ q, Zs q) = Z → (∀ q, AEMeasurable (fun t : ℝ => ∫⁻ x in ψ '' (Zs q ∩ F ⁻¹' {t}), φ x ∂μHE[n]) ∧ ∫⁻ t : ℝ, (∫⁻ x in ψ '' (Zs q ∩ F ⁻¹' {t}), φ x ∂μHE[n]) = ∫⁻ x in ψ '' Zs q, g x ∂μHE[n + 1]) → AEMeasurable (fun t : ℝ => ∫⁻ x in ψ '' (Z ∩ F ⁻¹' {t}), φ x ∂μHE[n]) ∧ ∫⁻ t : ℝ, (∫⁻ x in ψ '' (Z ∩ F ⁻¹' {t}), φ x ∂μHE[n]) = ∫⁻ x in ψ '' Z, g x ∂μHE[n + 1]`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
