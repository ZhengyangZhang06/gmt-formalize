# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.half_space_cone_lies_in_boundary-a1.imrep_support_eq_measure_support-a1.unit_orientation_nonzero_bounded-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-half-space-cone-lies-in-boundary-a1-imrep-support-eq-measure-sup-2d6f974584/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.half_space_cone_lies_in_boundary-a1.imrep_support_eq_measure_support-a1`
- Child key: `unit_orientation_nonzero_bounded`
- Declaration: `Submission.imsupp_unit_orientation_ne_zero_norm_le_one`
- Exact Lean type: `∀ (P n : ℕ) (ξ : MultiVector P n) (Q : Submodule ℝ (Euclid P)), IsUnitOrientationOf ξ Q → ξ ≠ 0 ∧ ‖ξ‖ ≤ 1`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
