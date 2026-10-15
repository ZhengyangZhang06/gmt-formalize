# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.slice_imreps-a1.coarea_ae_transfer-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-slicing-a1-s-4f507fe94c/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.slice_imreps-a1`
- Child key: `coarea_ae_transfer`
- Declaration: `Submission.dor_lmbsf_si_coarea_ae_transfer`
- Exact Lean type: `∀ (P : ℕ) (μ : Measure (Euclid P)) (ν : ℝ → Measure (Euclid P)) (w : Euclid P → ℝ≥0∞) (p : Euclid P → Prop), (∀ φ : Euclid P → ℝ≥0∞, Measurable φ → AEMeasurable (fun t => ∫⁻ x, φ x ∂(ν t)) ∧ ∫⁻ t, ∫⁻ x, φ x ∂(ν t) = ∫⁻ x, w x * φ x ∂μ) → (∀ᵐ x ∂μ, p x) → ∀ᵐ t, ∀ᵐ x ∂(ν t), p x`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
