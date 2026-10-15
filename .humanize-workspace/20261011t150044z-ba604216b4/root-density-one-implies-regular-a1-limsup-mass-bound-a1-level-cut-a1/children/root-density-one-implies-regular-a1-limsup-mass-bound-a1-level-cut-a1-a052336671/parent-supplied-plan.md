# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.limsup_mass_bound-a1.level_cut-a1.cut_cycle-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-level-cut-a1-a052336671/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.level_cut-a1`
- Child key: `cut_cycle`
- Declaration: `Submission.dor_lmb_glc_cut_cycle`
- Exact Lean type: `∀ (P n : ℕ) (U : Set (Euclid P)) (R : GeometricCurrentOn U (n + 1)) (RR : IMRep U (n + 1)) (RB : IMRep U n) (D Q : GeometricCurrentOn U n) (y : Euclid P) (t : ℝ), RR.Represents R → (∀ ω : TestFormOn U n, D ω = ∫ x in RB.carrier ∩ ball y t, (RB.mult x : ℝ) * RB.orient x ((ω : DifferentialForm (Euclid P) n) x) ∂μHE[n]) → (∀ ω : TestFormOn U n, Q ω = (∫ x in RR.carrier ∩ ball y t, (RR.mult x : ℝ) * RR.orient x (exteriorDerivative (ω : DifferentialForm (Euclid P) n) x) ∂μHE[n + 1]) - ∫ x in RB.carrier ∩ ball y t, (RB.mult x : ℝ) * RB.orient x ((ω : DifferentialForm (Euclid P) n) x) ∂μHE[n]) → ∃ X : GeometricCurrentOn U n, (∀ ω : TestFormOn U n, X ω = D ω + Q ω) ∧ BoundaryVanishes X ∧ (∀ ω : TestFormOn U n, Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) (closedBall y t) → X ω = 0) ∧ ∀ ω : TestFormOn U n, tsupport (ω : DifferentialForm (Euclid P) n) ⊆ ball y t → X ω = R.boundary ω`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
