# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.regular_components_are_minimizing-a1.integer_multiplicity_sub-a1.overlap_sign-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-components-are-minimizing-a1-integer-multiplicity-sub-a1-f90e8352bc/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.regular_components_are_minimizing-a1.integer_multiplicity_sub-a1`
- Child key: `overlap_sign`
- Declaration: `Submission.regcomp_ims_overlap_orient_eq_or_neg`
- Exact Lean type: `∀ (P n : ℕ) (U : Set (Euclid P)) (R₁ R₂ : IMRep U n), (∀ᵐ x ∂(μHE[n].restrict (R₁.carrier ∩ R₂.carrier)), ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n R₁.carrier x Q → HasApproximateTangentSpaceAt n (R₁.carrier ∩ R₂.carrier) x Q) → (∀ᵐ x ∂(μHE[n].restrict (R₁.carrier ∩ R₂.carrier)), ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n R₂.carrier x Q → HasApproximateTangentSpaceAt n (R₁.carrier ∩ R₂.carrier) x Q) → ∀ᵐ x ∂(μHE[n].restrict (R₁.carrier ∩ R₂.carrier)), R₂.orient x = R₁.orient x ∨ R₂.orient x = -R₁.orient x`

## Sibling prerequisites

- `root.regular_set_dense-a1.integer_combination-a1.orientation_sign-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
