# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.moving_blowups-a1.local_comparison-a1.retraction_comparison-a1.restrict_to_univ-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-local-compariso-5a45ed3919/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.moving_blowups-a1.local_comparison-a1.retraction_comparison-a1`
- Child key: `restrict_to_univ`
- Declaration: `Submission.dimred_mbl_lc_rc_restrict_to_univ`
- Exact Lean type: `∀ (P n : ℕ) (U E K : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), IsOpen U → R.Represents T → MeasurableSet E → IsCompact K → E ⊆ K → K ⊆ U → ∃ (Q : GeometricCurrentOn (univ : Set (Euclid P)) n) (RQ : IMRep (univ : Set (Euclid P)) n) (T₁ : GeometricCurrentOn U n) (R₁ : IMRep U n), RQ.Represents Q ∧ RQ.measure = R.measure.restrict E ∧ R₁.Represents T₁ ∧ R₁.measure = R.measure.restrict Eᶜ ∧ (∀ ω : TestFormOn U n, T ω = Q (testFormOnInclusion (subset_univ U) n ω) + T₁ ω) ∧ (∀ ω : TestFormOn U n, tsupport (ω : DifferentialForm (Euclid P) n) ⊆ E → Q (testFormOnInclusion (subset_univ U) n ω) = T ω) ∧ Q.support ⊆ closure E ∩ T.support ∧ IsCompact Q.support`

## Sibling prerequisites

- `root.density_one_implies_regular-a1.imrep_mass_and_support-a1`
- `root.compactness_of_minimizing_currents-a1.im_calculus-a1`
- `root.compactness_of_minimizing_currents-a1.local_comparison-a1.imrep_restriction-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
