# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.half_space_cone_lies_in_boundary-a1.cone_measure_homogeneous-a1.rescaled_imrep-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-half-space-cone-lies-in-boundary-a1-cone-measure-homogeneous-a1-558afe01a7/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.half_space_cone_lies_in_boundary-a1.cone_measure_homogeneous-a1`
- Child key: `rescaled_imrep`
- Declaration: `Submission.imrep_univ_smul_rescale_exists`
- Exact Lean type: `∀ (P n : ℕ) (R : IMRep (univ : Set (Euclid P)) n) (c : ℝ), 0 < c → ∃ R' : IMRep (univ : Set (Euclid P)) n, R'.carrier = (fun x => c • x) ⁻¹' R.carrier ∧ (∀ x, R'.mult x = R.mult (c • x)) ∧ ∀ x, R'.orient x = R.orient (c • x)`

## Sibling prerequisites

- `root.half_space_cone_lies_in_boundary-a1.cone_measure_homogeneous-a1.dilation_change_of_variables-a1`
- `root.half_space_cone_lies_in_boundary-a1.cone_measure_homogeneous-a1.tangent_space_dilation-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
