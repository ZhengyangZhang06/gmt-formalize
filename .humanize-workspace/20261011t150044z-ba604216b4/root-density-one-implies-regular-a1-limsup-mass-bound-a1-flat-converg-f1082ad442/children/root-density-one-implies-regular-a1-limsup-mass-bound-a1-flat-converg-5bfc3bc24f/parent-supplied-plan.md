# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.total_bounded-a1.extend_univ-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-flat-converg-5bfc3bc24f/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.total_bounded-a1`
- Child key: `extend_univ`
- Declaration: `Submission.dor_lmb_fc_tb_extend_univ`
- Exact Lean type: `∀ (P d : ℕ) (U K : Set (Euclid P)) (A : GeometricCurrentOn U d), IsOpen U → IsCompact K → K ⊆ U → IsIntegerMultiplicity A → (∀ ω : TestFormOn U d, Disjoint (tsupport (ω : DifferentialForm (Euclid P) d)) K → A ω = 0) → ∃ Y : GeometricCurrentOn (univ : Set (Euclid P)) d, IsIntegerMultiplicity Y ∧ Y.restrictDomain (subset_univ U) = A ∧ (∀ ω : TestFormOn (univ : Set (Euclid P)) d, Disjoint (tsupport (ω : DifferentialForm (Euclid P) d)) K → Y ω = 0) ∧ Y.mass ≤ A.mass`

## Sibling prerequisites

- `root.density_one_implies_regular-a1.imrep_mass_and_support-a1`
- `root.compactness_of_minimizing_currents-a1.im_calculus-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
