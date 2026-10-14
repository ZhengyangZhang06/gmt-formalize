# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.moving_blowups-a1.pushforward-a1.orient_comp-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-pushforward-a1-43165fa562/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.moving_blowups-a1.pushforward-a1`
- Child key: `orient_comp`
- Declaration: `Submission.dimred_mbl_pf_unitOrientation_comp`
- Exact Lean type: `∀ (P n : ℕ) (ξ : MultiVector P n) (Q : Submodule ℝ (Euclid P)) (L : Euclid P →L[ℝ] Euclid P), IsUnitOrientationOf ξ Q → (∀ α : Covector (Euclid P) n, |ξ (α.compContinuousLinearMap L)| ≤ covectorEuclideanNorm α * ‖L‖ ^ n) ∧ ((∀ v ∈ Q, L v = v) → ∀ α : Covector (Euclid P) n, ξ (α.compContinuousLinearMap L) = ξ α)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
