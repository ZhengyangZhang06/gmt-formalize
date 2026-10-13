# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.zero_dim_minimizing_trivial-a1.imrep_zero_erase_point-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-zero-dim-minimizing-trivial-a1-im-66bc505ba7/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.zero_dim_minimizing_trivial-a1`
- Child key: `imrep_zero_erase_point`
- Declaration: `Submission.dor_zdm_imrep_zero_erase_point`
- Exact Lean type: `∀ (P : ℕ) (U : Set (Euclid P)) (R : IMRep U 0) (x : Euclid P), x ∈ R.carrier → ∃ R' : IMRep U 0, R'.carrier = R.carrier \ {x} ∧ R.measure = R'.measure + (R.mult x : ℝ≥0∞) • Measure.dirac x ∧ ∀ ω : TestFormOn U 0, R'.action (ω : DifferentialForm (Euclid P) 0) = R.action (ω : DifferentialForm (Euclid P) 0) - (R.mult x : ℝ) * R.orient x ((ω : DifferentialForm (Euclid P) 0) x)`

## Sibling prerequisites

- `root.density_one_implies_regular-a1.zero_dim_minimizing_trivial-a1.imrep_zero_structure-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
