# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.half_space_cone_lies_in_boundary-a1.imrep_support_eq_measure_support-a1.weight_null_where_current_vanishes-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-half-space-cone-lies-in-boundary-a1-imrep-support-eq-measure-sup-a40c945682/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.half_space_cone_lies_in_boundary-a1.imrep_support_eq_measure_support-a1`
- Child key: `weight_null_where_current_vanishes`
- Declaration: `Submission.imsupp_measure_eq_zero_of_vanishesOn`
- Exact Lean type: `∀ (P n : ℕ) (U W : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), R.Represents T → IsOpen W → W ⊆ U → T.VanishesOn W → R.measure W = 0`

## Sibling prerequisites

- `root.half_space_cone_lies_in_boundary-a1.imrep_support_eq_measure_support-a1.unit_orientation_nonzero_bounded-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
