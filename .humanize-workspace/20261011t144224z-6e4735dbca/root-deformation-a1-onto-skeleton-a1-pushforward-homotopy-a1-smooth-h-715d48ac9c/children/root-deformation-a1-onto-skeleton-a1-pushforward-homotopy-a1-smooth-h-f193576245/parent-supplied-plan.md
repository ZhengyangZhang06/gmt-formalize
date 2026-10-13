# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.smooth_homotopy-a1.interior_bound-a1.contraction_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-onto-skeleton-a1-pushforward-homotopy-a1-smooth-h-f193576245/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.smooth_homotopy-a1.interior_bound-a1`
- Child key: `contraction_bound`
- Declaration: `Submission.dph_sh_ib_covectorEuclideanNorm_contract_le`
- Exact Lean type: `∀ (p k : ℕ) (γ : Covector (Eucl p) (k + 1)) (w : Eucl p) (δ : Covector (Eucl p) k), (∀ u : Fin k → Eucl p, δ u = γ (Fin.cons w u)) → covectorEuclideanNorm δ ≤ Real.sqrt ((k : ℝ) + 1) * ‖w‖ * covectorEuclideanNorm γ`

## Sibling prerequisites

- `root.integrality_weak_limits-a1.smooth_pushforward-a1.pullback_norm-a1.tuple_sum_factorial-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
