# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.pointwise_identity-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-slicing-a1-p-c4ce07b362/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1`
- Child key: `pointwise_identity`
- Declaration: `Submission.dor_lmbs_slice_identity_of_averages`
- Exact Lean type: `∀ (P n : ℕ) (U : Set (Euclid P)) (RT : IMRep U (n + 1)) (RB : IMRep U n) (Rs : ℝ → IMRep U n) (f : Euclid P → ℝ), IsOpen U → Measurable f → (∀ ω : TestFormOn U n, LocallyIntegrable (fun s => (Rs s).action (ω : DifferentialForm (Euclid P) n))) → (∀ (ω : TestFormOn U n) (a b : ℝ), a < b → ∫ s in a..b, (Rs s).action (ω : DifferentialForm (Euclid P) n) = (b - a) * ((∫ x in RT.carrier, (RT.mult x : ℝ) * min 1 (max 0 ((b - f x) / (b - a))) * RT.orient x (exteriorDerivative (ω : DifferentialForm (Euclid P) n) x) ∂μHE[n + 1]) - ∫ x in RB.carrier, (RB.mult x : ℝ) * min 1 (max 0 ((b - f x) / (b - a))) * RB.orient x ((ω : DifferentialForm (Euclid P) n) x) ∂μHE[n])) → ∀ᵐ t, ∀ ω : TestFormOn U n, (Rs t).action (ω : DifferentialForm (Euclid P) n) = (∫ x in RT.carrier ∩ {x | f x < t}, (RT.mult x : ℝ) * RT.orient x (exteriorDerivative (ω : DifferentialForm (Euclid P) n) x) ∂μHE[n + 1]) - ∫ x in RB.carrier ∩ {x | f x < t}, (RB.mult x : ℝ) * RB.orient x ((ω : DifferentialForm (Euclid P) n) x) ∂μHE[n]`

## Sibling prerequisites

- `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.testform_dense-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
