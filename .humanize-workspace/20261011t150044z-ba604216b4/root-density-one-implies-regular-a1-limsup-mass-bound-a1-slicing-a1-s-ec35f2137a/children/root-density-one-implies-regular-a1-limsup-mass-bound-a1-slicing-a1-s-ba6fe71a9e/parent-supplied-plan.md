# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.piece_coarea-a1.param_coarea-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-slicing-a1-s-ba6fe71a9e/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.piece_coarea-a1`
- Child key: `param_coarea`
- Declaration: `Submission.dor_lmbsf_pc_param_coarea`
- Exact Lean type: `∀ (P n : ℕ) (Φ : Euclid (n + 1) → Euclid P) (S : Set (Euclid (n + 1))) (G : Euclid P → Euclid P), MeasurableSet S → (∀ w ∈ S, DifferentiableAt ℝ Φ w) → (∀ w ∈ S, Injective (fderiv ℝ Φ w)) → InjOn Φ S → (∀ w ∈ S, G (Φ w) ∈ LinearMap.range (fderiv ℝ Φ w : Euclid (n + 1) →ₗ[ℝ] Euclid P) ∧ ∀ e : Euclid (n + 1), inner ℝ (G (Φ w)) (fderiv ℝ Φ w e) = e 0) → ∀ φ : Euclid P → ℝ≥0∞, Measurable φ → AEMeasurable (fun t : ℝ => ∫⁻ x in Φ '' (S ∩ {w | w 0 = t}), φ x ∂μHE[n]) ∧ ∫⁻ t : ℝ, (∫⁻ x in Φ '' (S ∩ {w | w 0 = t}), φ x ∂μHE[n]) = ∫⁻ x in Φ '' S, ‖G x‖ₑ * φ x ∂μHE[n + 1]`

## Sibling prerequisites

- `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.piece_coarea-a1.gram_cofactor-a1`
- `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.piece_coarea-a1.slice_tonelli-a1`
- `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.local_unit_rep-a1.area_formula-a1.gram_area-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
