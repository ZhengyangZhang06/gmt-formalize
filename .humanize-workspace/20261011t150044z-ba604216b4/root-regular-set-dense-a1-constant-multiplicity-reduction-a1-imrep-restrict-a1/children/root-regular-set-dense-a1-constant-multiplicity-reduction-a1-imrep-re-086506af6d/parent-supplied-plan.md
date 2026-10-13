# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.regular_set_dense-a1.constant_multiplicity_reduction-a1.imrep_restrict-a1.approx_tangent_local_null-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-set-dense-a1-constant-multiplicity-reduction-a1-imrep-re-086506af6d/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.regular_set_dense-a1.constant_multiplicity_reduction-a1.imrep_restrict-a1`
- Child key: `approx_tangent_local_null`
- Declaration: `Submission.rsd_cmr_ir_approxTangent_of_local_null`
- Exact Lean type: `∀ (P n : ℕ) (M M' : Set (Euclid P)) (x : Euclid P) (δ : ℝ) (Q : Submodule ℝ (Euclid P)), MeasurableSet M → M' ⊆ M → 0 < δ → μHE[n] ((M \ M') ∩ ball x δ) = 0 → HasApproximateTangentSpaceAt n M x Q → HasApproximateTangentSpaceAt n M' x Q`

## Sibling prerequisites

- `root.regular_set_dense-a1.constant_multiplicity_reduction-a1.imrep_restrict-a1.blowup_image_measure-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
