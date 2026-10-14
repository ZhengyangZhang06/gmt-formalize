# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.tangential_gradient-a1.coarea_gluing-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-slicing-a1-s-19616098d1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.tangential_gradient-a1`
- Child key: `coarea_gluing`
- Declaration: `Submission.dor_lmbsf_tg_coarea_gluing`
- Exact Lean type: `∀ (P : ℕ) (μ ν : Measure (Euclid P)) (M : Set (Euclid P)) (S : ℕ → Set (Euclid P)) (g : Euclid P → Euclid P) (f : Euclid P → ℝ) (φ : Euclid P → ℝ≥0∞), MeasurableSet M → (∀ j, MeasurableSet (S j)) → Pairwise (fun i j => Disjoint (S i) (S j)) → (∀ j, S j ⊆ M) → Measurable g → (∀ x, (∀ j, x ∉ S j) → g x = 0) → Measurable f → (∀ j, AEMeasurable (fun t => ∫⁻ x in S j ∩ {x | g x ≠ 0} ∩ f ⁻¹' {t}, φ x ∂ν) ∧ ∫⁻ t, (∫⁻ x in S j ∩ {x | g x ≠ 0} ∩ f ⁻¹' {t}, φ x ∂ν) = ∫⁻ x in S j, ‖g x‖ₑ * φ x ∂μ) → AEMeasurable (fun t => ∫⁻ x in M ∩ {x | g x ≠ 0} ∩ f ⁻¹' {t}, φ x ∂ν) ∧ ∫⁻ t, (∫⁻ x in M ∩ {x | g x ≠ 0} ∩ f ⁻¹' {t}, φ x ∂ν) = ∫⁻ x in M, ‖g x‖ₑ * φ x ∂μ`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
