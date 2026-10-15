# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.slice_imreps-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-slicing-a1-s-7a19fe4708/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1`
- Child key: `slice_imreps`
- Declaration: `Submission.dor_lmbsf_slice_imreps`
- Exact Lean type: `∀ (P n : ℕ) (U : Set (Euclid P)) (RT : IMRep U (n + 1)) (f : Euclid P → ℝ) (L : NNReal) (g : Euclid P → Euclid P), IsOpen U → LipschitzWith L f → Measurable g → (∀ x, ‖g x‖ ≤ L) → (∀ᵐ x ∂(μHE[n + 1].restrict RT.carrier), g x ∈ approxTangentPlane (n + 1) RT.carrier x) → (∀ φ : Euclid P → ℝ≥0∞, Measurable φ → AEMeasurable (fun t => ∫⁻ x in RT.carrier ∩ {x | g x ≠ 0} ∩ f ⁻¹' {t}, φ x ∂μHE[n]) ∧ ∫⁻ t, (∫⁻ x in RT.carrier ∩ {x | g x ≠ 0} ∩ f ⁻¹' {t}, φ x ∂μHE[n]) = ∫⁻ x in RT.carrier, ‖g x‖ₑ * φ x ∂μHE[n + 1]) → (∀ t, CountablyRectifiable n (RT.carrier ∩ {x | g x ≠ 0} ∩ f ⁻¹' {t})) → (∀ t, (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (RT.carrier ∩ {x | g x ≠ 0} ∩ f ⁻¹' {t} ∩ K) ≠ ∞) → ∀ᵐ x ∂(μHE[n].restrict (RT.carrier ∩ {x | g x ≠ 0} ∩ f ⁻¹' {t})), HasApproximateTangentSpaceAt n (RT.carrier ∩ {x | g x ≠ 0} ∩ f ⁻¹' {t}) x (approxTangentPlane (n + 1) RT.carrier x ⊓ (ℝ ∙ g x)ᗮ)) → ∃ Rs : ℝ → IMRep U n, (∀ t, (Rs t).carrier ⊆ f ⁻¹' {t}) ∧ (∀ W : Set (Euclid P), MeasurableSet W → AEMeasurable (fun t => (Rs t).measure W) ∧ ∫⁻ t, (Rs t).measure W ≤ (L : ℝ≥0∞) * RT.measure W) ∧ (∀ ω : TestFormOn U n, Integrable (fun s => (Rs s).action (ω : DifferentialForm (Euclid P) n))) ∧ ∀ (ω : TestFormOn U n) (a b : ℝ), a < b → ∫ s in a..b, (Rs s).action (ω : DifferentialForm (Euclid P) n) = ∫ x in RT.carrier ∩ {x | a < f x ∧ f x < b}, (RT.mult x : ℝ) * RT.orient x (ContinuousAlternatingMap.alternatizeUncurryFin ((innerSL ℝ (g x)).smulRight ((ω : DifferentialForm (Euclid P) n) x))) ∂μHE[n + 1]`

## Sibling prerequisites

- `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.wedge_orientation-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
