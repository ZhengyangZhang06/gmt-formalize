# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.zero_dim_vanishing-a1.erase_point-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-zero-dim-vanishing-a1-erase-point-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.zero_dim_vanishing-a1`
- Child key: `erase_point`
- Declaration: `Submission.dimred_zdv_erase_point`
- Exact Lean type: `∀ (P : ℕ) (U : Set (Euclid P)) (R : IMRep U 0) (p : Euclid P), p ∈ R.carrier → ∃ R' : IMRep U 0, R'.carrier = R.carrier \ {p} ∧ R'.mult = R.mult ∧ R'.orient = R.orient ∧ ∀ ω : TestFormOn U 0, R.action (ω : DifferentialForm (Euclid P) 0) = R'.action (ω : DifferentialForm (Euclid P) 0) + (R.mult p : ℝ) * R.orient p ((ω : DifferentialForm (Euclid P) 0) p)`

## Sibling prerequisites

- `root.dimension_reduction_results-a1.zero_dim_vanishing-a1.carrier_finite-a1`
- `root.dimension_reduction_results-a1.zero_dim_vanishing-a1.tangent_erase-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
