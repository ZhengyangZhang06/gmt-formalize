# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.limsup_mass_bound-a1.level_cut-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-level-cut-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1`
- Child key: `level_cut`
- Declaration: `Submission.dor_lmb_good_level_cut`
- Exact Lean type: `(∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), IsOpen U → R.Represents T → (∀ W : Set (Euclid P), IsOpen W → T.massOn W = R.measure W) ∧ T.support = U ∩ R.measure.support) → ∀ (P n : ℕ) (U : Set (Euclid P)) (T T' S : GeometricCurrentOn U n) (R : GeometricCurrentOn U (n + 1)) (y : Euclid P) (ρ ρ' : ℝ), IsOpen U → 0 < n → IsIntegerMultiplicity T → IsIntegerMultiplicity T' → IsIntegerMultiplicity S → IsIntegerMultiplicity R → (∀ ω : TestFormOn U n, T ω - T' ω = R.boundary ω + S ω) → 0 < ρ → ρ < ρ' → closedBall y ρ' ⊆ U → ∃ (t : ℝ) (X Y : GeometricCurrentOn U n) (RY : IMRep U n), ρ < t ∧ t < ρ' ∧ IsIntegerMultiplicity X ∧ BoundaryVanishes X ∧ (∀ ω : TestFormOn U n, Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) (closedBall y t) → X ω = 0) ∧ (∀ ω : TestFormOn U n, Y ω = T' ω + X ω) ∧ RY.Represents Y ∧ RY.measure (closedBall y t) ≤ T.massOn (ball y ρ') + S.massOn (ball y ρ') + ENNReal.ofReal (2 / (ρ' - ρ)) * R.massOn (ball y ρ')`

## Sibling prerequisites

- `root.density_one_implies_regular-a1.limsup_mass_bound-a1.int_combination-a1`
- `root.density_one_implies_regular-a1.limsup_mass_bound-a1.borel_restriction-a1`
- `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
