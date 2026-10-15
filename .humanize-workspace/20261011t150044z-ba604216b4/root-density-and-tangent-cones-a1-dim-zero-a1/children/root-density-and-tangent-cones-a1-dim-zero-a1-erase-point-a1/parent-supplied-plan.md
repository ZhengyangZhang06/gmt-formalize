# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_and_tangent_cones-a1.dim_zero-a1.erase_point-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-dim-zero-a1-erase-point-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_and_tangent_cones-a1.dim_zero-a1`
- Child key: `erase_point`
- Declaration: `Submission.dtc_dim_zero_erase_point`
- Exact Lean type: `∀ (P : ℕ) (U : Set (Euclid P)) (R : IMRep U 0) (p : Euclid P), p ∈ R.carrier → ∃ R' : IMRep U 0, R'.carrier = R.carrier \ {p} ∧ R'.mult = R.mult ∧ R'.orient = R.orient ∧ R.measure = R'.measure + (R.mult p : ℝ≥0∞) • Measure.dirac p ∧ ∀ ω : TestFormOn U 0, R.action (ω : DifferentialForm (Euclid P) 0) = R'.action (ω : DifferentialForm (Euclid P) 0) + (R.mult p : ℝ) * R.orient p ((ω : DifferentialForm (Euclid P) 0) p)`

## Sibling prerequisites

- `root.density_and_tangent_cones-a1.dim_zero-a1.carrier_finite-a1`
- `root.density_and_tangent_cones-a1.dim_zero-a1.tangent_delete_point-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
