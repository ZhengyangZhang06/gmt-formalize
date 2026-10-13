# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.moving_blowups-a1.pushforward-a1.pf_current-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-pushforward-a1-9eb1427eef/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.moving_blowups-a1.pushforward-a1`
- Child key: `pf_current`
- Declaration: `Submission.dimred_mbl_pf_pushforward_current_exists`
- Exact Lean type: `∀ (P n : ℕ) (U K O : Set (Euclid P)) (R : IMRep U n) (f : Euclid P → Euclid P), IsOpen U → IsCompact K → K ⊆ U → μHE[n] (R.carrier \ K) = 0 → IsOpen O → K ⊆ O → ContDiffOn ℝ 1 f O → f '' K ⊆ U → ∃ Q : GeometricCurrentOn U n, (∀ ω : TestFormOn U n, Q ω = ∫ x in R.carrier, (R.mult x : ℝ) * R.orient x (((ω : DifferentialForm (Euclid P) n) (f x)).compContinuousLinearMap (fderiv ℝ f x)) ∂μHE[n]) ∧ IsCompact Q.support ∧ Q.support ⊆ f '' K`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
