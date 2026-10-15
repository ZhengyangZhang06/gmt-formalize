# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.skeleton_deformation-a1.lipschitz_extension-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-deformation-the-8bada4ae1c/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.skeleton_deformation-a1`
- Child key: `lipschitz_extension`
- Declaration: `Submission.dimred_mbl_dtsd_lipschitz_extension`
- Exact Lean type: `∀ (P : ℕ) (S : Set (Euclid P)) (ψ : Euclid P → Euclid P) (K : NNReal), LipschitzOnWith K ψ S → ∃ φ : Euclid P → Euclid P, LipschitzWith (NNReal.sqrt P * K) φ ∧ EqOn φ ψ S`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
