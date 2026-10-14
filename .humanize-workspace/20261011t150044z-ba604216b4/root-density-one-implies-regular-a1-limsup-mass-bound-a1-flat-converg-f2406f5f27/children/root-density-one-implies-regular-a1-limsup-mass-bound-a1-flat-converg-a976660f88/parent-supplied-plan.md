# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.skeleton_deformation-a1.good_slice-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-flat-converg-a976660f88/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.skeleton_deformation-a1`
- Child key: `good_slice`
- Declaration: `Submission.dor_lmb_fcd_sd_good_slice`
- Exact Lean type: `∀ (P m : ℕ) (T : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)) (RT : IMRep (univ : Set (Euclid P)) (m + 1)) (RB : IMRep (univ : Set (Euclid P)) m) (f : Euclid P → ℝ) (L : NNReal) (Ps : ℝ → GeometricCurrentOn (univ : Set (Euclid P)) m) (a b : ℝ), RT.Represents T → Continuous f → a < b → (∀ W : Set (Euclid P), IsOpen W → AEMeasurable (fun t => (Ps t).massOn W) ∧ ∫⁻ t, (Ps t).massOn W ≤ (L : ℝ≥0∞) * T.massOn W) → (∀ᵐ t, IsIntegerMultiplicity (Ps t) ∧ (∀ ω : TestFormOn (univ : Set (Euclid P)) m, Disjoint (tsupport (ω : DifferentialForm (Euclid P) m)) (f ⁻¹' {t}) → Ps t ω = 0) ∧ ∀ ω : TestFormOn (univ : Set (Euclid P)) m, Ps t ω = (∫ x in RT.carrier ∩ {x | f x < t}, (RT.mult x : ℝ) * RT.orient x (exteriorDerivative (ω : DifferentialForm (Euclid P) m) x) ∂μHE[m + 1]) - ∫ x in RB.carrier ∩ {x | f x < t}, (RB.mult x : ℝ) * RB.orient x ((ω : DifferentialForm (Euclid P) m) x) ∂μHE[m]) → ∃ t ∈ Ioo a b, IsIntegerMultiplicity (Ps t) ∧ (∀ ω : TestFormOn (univ : Set (Euclid P)) m, Disjoint (tsupport (ω : DifferentialForm (Euclid P) m)) (f ⁻¹' {t}) → Ps t ω = 0) ∧ (∀ ω : TestFormOn (univ : Set (Euclid P)) m, Ps t ω = (∫ x in RT.carrier ∩ {x | f x < t}, (RT.mult x : ℝ) * RT.orient x (exteriorDerivative (ω : DifferentialForm (Euclid P) m) x) ∂μHE[m + 1]) - ∫ x in RB.carrier ∩ {x | f x < t}, (RB.mult x : ℝ) * RB.orient x ((ω : DifferentialForm (Euclid P) m) x) ∂μHE[m]) ∧ ENNReal.ofReal (b - a) * (Ps t).mass ≤ 2 * ((L : ℝ≥0∞) * RT.measure {x | a < f x ∧ f x < b})`

## Sibling prerequisites

- `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.skeleton_deformation-a1.markov_point-a1`
- `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.skeleton_deformation-a1.im_concentrated-a1`
- `root.density_one_implies_regular-a1.imrep_mass_and_support-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
