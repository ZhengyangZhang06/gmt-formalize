# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation_top-a1.cutoff_pullback-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-flat-converg-3abc140ad4/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation_top-a1`
- Child key: `cutoff_pullback`
- Declaration: `Submission.dor_lmb_fc_dtop_cutoff_pullback`
- Exact Lean type: `∀ (P d : ℕ) (p : Euclid (P + 1) →L[ℝ] Euclid P), (∀ (y : Euclid (P + 1)) (i : Fin P), p y i = y (Fin.castSucc i)) → ∀ K : Set (Euclid (P + 1)), IsCompact K → ∃ (V : Set (Euclid (P + 1))) (E : TestFormOn (univ : Set (Euclid P)) d →ₗ[ℝ] TestFormOn (univ : Set (Euclid (P + 1))) d), IsOpen V ∧ K ⊆ V ∧ (∀ (ω : TestFormOn (univ : Set (Euclid P)) d) (y : Euclid (P + 1)), y ∈ V → (E ω : DifferentialForm (Euclid (P + 1)) d) y = ((ω : DifferentialForm (Euclid P) d) (p y)).compContinuousLinearMap p) ∧ (∀ (ω : TestFormOn (univ : Set (Euclid P)) d) (y : Euclid (P + 1)), y ∈ V → exteriorDerivative (E ω : DifferentialForm (Euclid (P + 1)) d) y = (exteriorDerivative (ω : DifferentialForm (Euclid P) d) (p y)).compContinuousLinearMap p) ∧ (∀ ω : TestFormOn (univ : Set (Euclid P)) d, tsupport (E ω : DifferentialForm (Euclid (P + 1)) d) ⊆ p ⁻¹' tsupport (ω : DifferentialForm (Euclid P) d)) ∧ (∀ (ω : TestFormOn (univ : Set (Euclid P)) d) (y : Euclid (P + 1)), covectorEuclideanNorm ((E ω : DifferentialForm (Euclid (P + 1)) d) y) ≤ covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) d) (p y))) ∧ ∀ ωs : ℕ → TestFormOn (univ : Set (Euclid P)) d, TestFormOnConverges ωs 0 → TestFormOnConverges (fun j => E (ωs j)) 0`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
