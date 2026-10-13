# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.moving_blowups-a1.blowup_hypotheses-a1.local_retraction-a1.left_inverse_projection-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-blowup-hypothes-21b53d5dee/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.moving_blowups-a1.blowup_hypotheses-a1.local_retraction-a1`
- Child key: `left_inverse_projection`
- Declaration: `Submission.dimred_mbl_bh_lr_left_inverse_projection`
- Exact Lean type: `∀ (P d : ℕ) (L : Euclid d →L[ℝ] Euclid P), Injective L → ∃ A : Euclid P →L[ℝ] Euclid d, A.comp L = ContinuousLinearMap.id ℝ (Euclid d) ∧ ‖L.comp A‖ ≤ 1`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
