# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.retraction_comparison-a1.ambient_restriction-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-14ae52ec9c/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.retraction_comparison-a1`
- Child key: `ambient_restriction`
- Declaration: `Submission.dtc_bc_lc_rc_ambient_restriction`
- Exact Lean type: `∀ (P n : ℕ) (U W : Set (Euclid P)) (S : GeometricCurrentOn U n) (R : IMRep U n), IsOpen U → IsOpen W → CompactlyContained W U → R.Represents S → ∃ (Q : GeometricCurrentOn (univ : Set (Euclid P)) n) (RQ : IMRep (univ : Set (Euclid P)) n), RQ.Represents Q ∧ RQ.carrier = R.carrier ∩ W ∧ RQ.mult = R.mult ∧ RQ.orient = R.orient ∧ (∀ ω : TestFormOn U n, tsupport (ω : DifferentialForm (Euclid P) n) ⊆ W → Q (testFormOnInclusion (subset_univ U) n ω) = S ω) ∧ Q.support ⊆ closure W ∩ S.support ∧ IsCompact Q.support`

## Sibling prerequisites

- `root.compactness_of_minimizing_currents-a1.im_calculus-a1`
- `root.density_and_tangent_cones-a1.mass_eq_measure-a1`
- `root.density_and_tangent_cones-a1.vanish_off_support-a1`
- `root.regular_set_dense-a1.constant_multiplicity_reduction-a1.support_of_vanishing-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
