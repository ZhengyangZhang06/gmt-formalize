# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.integrality_weak_limits-a1.smooth_pushforward-a1.pullback_norm-a1.one_slot_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-smooth-pushforward-a1-pullback-norm-a-76834dc165/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.integrality_weak_limits-a1.smooth_pushforward-a1.pullback_norm-a1`
- Child key: `one_slot_bound`
- Declaration: `Submission.iwl_sp_pn_sum_sq_comp_basis_le`
- Exact Lean type: `∀ (P Q : ℕ) (L : Eucl P →L[ℝ] Eucl Q) (f : Eucl Q →ₗ[ℝ] ℝ), ∑ a : Fin P, (f (L (EuclideanSpace.basisFun (Fin P) ℝ a))) ^ 2 ≤ ‖L‖ ^ 2 * ∑ b : Fin Q, (f (EuclideanSpace.basisFun (Fin Q) ℝ b)) ^ 2`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
