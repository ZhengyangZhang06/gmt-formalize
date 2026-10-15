# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.skeleton_deformation-a1.im_restrict-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-flat-converg-ee137eb22e/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.skeleton_deformation-a1`
- Child key: `im_restrict`
- Declaration: `Submission.dor_lmb_fcd_sd_im_restrict`
- Exact Lean type: `∀ (P k : ℕ) (R : IMRep (univ : Set (Euclid P)) k), (∀ β : DifferentialForm (Euclid P) k, IsTestForm β → IntegrableOn (fun x => (R.mult x : ℝ) * R.orient x (β x)) R.carrier μHE[k]) ∧ ∀ (X : GeometricCurrentOn (univ : Set (Euclid P)) k) (F B : Set (Euclid P)), R.Represents X → IsClosed F → (∀ ω : TestFormOn (univ : Set (Euclid P)) k, Disjoint (tsupport (ω : DifferentialForm (Euclid P) k)) (F) → X ω = 0) → MeasurableSet B → ∃ Y : GeometricCurrentOn (univ : Set (Euclid P)) k, IsIntegerMultiplicity Y ∧ (∀ ω : TestFormOn (univ : Set (Euclid P)) k, Y ω = ∫ x in R.carrier ∩ B, (R.mult x : ℝ) * R.orient x ((ω : DifferentialForm (Euclid P) k) x) ∂μHE[k]) ∧ Y.mass = R.measure B ∧ ∀ ω : TestFormOn (univ : Set (Euclid P)) k, Disjoint (tsupport (ω : DifferentialForm (Euclid P) k)) (F ∩ B) → Y ω = 0`

## Sibling prerequisites

- `root.density_one_implies_regular-a1.imrep_mass_and_support-a1`
- `root.compactness_of_minimizing_currents-a1.im_calculus-a1`
- `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.skeleton_deformation-a1.im_concentrated-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
