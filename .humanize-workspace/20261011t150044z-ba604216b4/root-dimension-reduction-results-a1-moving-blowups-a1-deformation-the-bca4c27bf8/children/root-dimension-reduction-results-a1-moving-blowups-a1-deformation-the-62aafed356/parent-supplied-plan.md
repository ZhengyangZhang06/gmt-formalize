# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.face_replacement-a1.current_calculus-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-deformation-the-62aafed356/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.face_replacement-a1`
- Child key: `current_calculus`
- Declaration: `Submission.dimred_mbl_dtfr_current_calculus`
- Exact Lean type: `(∀ (P n : ℕ) (U W : Set (Euclid P)) (A B : GeometricCurrentOn U n), (A - B).support ⊆ A.support ∪ B.support ∧ (A - B).massOn W ≤ A.massOn W + B.massOn W) ∧ ∀ (P m : ℕ) (U : Set (Euclid P)) (A B : GeometricCurrentOn U (m + 1)), A.boundary.support ⊆ A.support ∧ (A - B).boundary = A.boundary - B.boundary`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
