# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-flat-convergence-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1`
- Child key: `flat_convergence`
- Declaration: `Submission.dor_lmb_flat_convergence_cycles`
- Exact Lean type: `(∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), IsOpen U → R.Represents T → (∀ W : Set (Euclid P), IsOpen W → T.massOn W = R.measure W) ∧ T.support = U ∩ R.measure.support) → ∀ (P n : ℕ) (U : Set (Euclid P)) (Ts : ℕ → GeometricCurrentOn U n) (T : GeometricCurrentOn U n), IsOpen U → 0 < n → (∀ j, IsIntegerMultiplicity (Ts j)) → IsIntegerMultiplicity T → (∀ j, BoundaryVanishes (Ts j)) → BoundaryVanishes T → (∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → ⨆ j, (Ts j).massOn W < ∞) → WeaklyConvergesOn Ts T → ∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → ∃ (Rs : ℕ → GeometricCurrentOn U (n + 1)) (Ss : ℕ → GeometricCurrentOn U n), (∀ j, IsIntegerMultiplicity (Rs j)) ∧ (∀ j, IsIntegerMultiplicity (Ss j)) ∧ (∀ j (ω : TestFormOn U n), T ω - Ts j ω = (Rs j).boundary ω + Ss j ω) ∧ Tendsto (fun j => (Rs j).massOn W + (Ss j).massOn W) atTop (𝓝 0)`

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
