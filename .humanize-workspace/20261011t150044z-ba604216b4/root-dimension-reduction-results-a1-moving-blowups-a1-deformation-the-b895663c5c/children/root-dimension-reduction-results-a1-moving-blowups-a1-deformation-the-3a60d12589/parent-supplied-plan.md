# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.face_replacement-a1.plane_orientation-a1.frame_sign-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-deformation-the-3a60d12589/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.face_replacement-a1.plane_orientation-a1`
- Child key: `frame_sign`
- Declaration: `Submission.dimred_mbl_dtfrpo_orthonormal_frame_sign`
- Exact Lean type: `∀ (P n : ℕ) (τ e : Fin n → Euclid P), Orthonormal ℝ τ → Orthonormal ℝ e → Submodule.span ℝ (Set.range τ) = Submodule.span ℝ (Set.range e) → (∀ α : Covector (Euclid P) n, α τ = α e) ∨ (∀ α : Covector (Euclid P) n, α τ = -α e)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
