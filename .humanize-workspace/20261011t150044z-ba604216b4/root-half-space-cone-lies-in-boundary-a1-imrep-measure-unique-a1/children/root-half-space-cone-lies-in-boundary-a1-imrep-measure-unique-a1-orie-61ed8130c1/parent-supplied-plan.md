# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.half_space_cone_lies_in_boundary-a1.imrep_measure_unique-a1.orientation_common_covector-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-half-space-cone-lies-in-boundary-a1-imrep-measure-unique-a1-orie-61ed8130c1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.half_space_cone_lies_in_boundary-a1.imrep_measure_unique-a1`
- Child key: `orientation_common_covector`
- Declaration: `Submission.unit_orientations_common_unit_covector`
- Exact Lean type: `∀ (P n : ℕ) (Q : Submodule ℝ (Euclid P)) (ξ₁ ξ₂ : MultiVector P n), IsUnitOrientationOf ξ₁ Q → IsUnitOrientationOf ξ₂ Q → ∃ α : Covector (Euclid P) n, |ξ₁ α| = 1 ∧ |ξ₂ α| = 1`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
