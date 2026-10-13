# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.total_bounded-a1.eq_of_vanish_off-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-flat-converg-85271bf7b4/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.total_bounded-a1`
- Child key: `eq_of_vanish_off`
- Declaration: `Submission.dor_lmb_fc_tb_eq_of_vanish_off`
- Exact Lean type: `∀ (P d : ℕ) (U K : Set (Euclid P)) (X Y : GeometricCurrentOn (univ : Set (Euclid P)) d), IsOpen U → IsCompact K → K ⊆ U → (∀ ω : TestFormOn (univ : Set (Euclid P)) d, Disjoint (tsupport (ω : DifferentialForm (Euclid P) d)) K → X ω = 0) → (∀ ω : TestFormOn (univ : Set (Euclid P)) d, Disjoint (tsupport (ω : DifferentialForm (Euclid P) d)) K → Y ω = 0) → X.restrictDomain (subset_univ U) = Y.restrictDomain (subset_univ U) → X = Y`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
