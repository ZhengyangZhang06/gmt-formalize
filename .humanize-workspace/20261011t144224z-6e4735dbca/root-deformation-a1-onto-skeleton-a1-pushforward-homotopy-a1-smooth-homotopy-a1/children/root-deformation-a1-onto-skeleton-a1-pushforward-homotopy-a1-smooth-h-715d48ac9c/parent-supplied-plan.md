# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.smooth_homotopy-a1.interior_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-onto-skeleton-a1-pushforward-homotopy-a1-smooth-h-715d48ac9c/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.smooth_homotopy-a1`
- Child key: `interior_bound`
- Declaration: `Submission.dph_sh_covectorEuclideanNorm_interior_le`
- Exact Lean type: `∀ (m m' k : ℕ) (γ : Covector (Eucl m') (k + 1)) (w : Eucl m') (T : Eucl m →L[ℝ] Eucl m') (a : ℝ) (β : Covector (Eucl m) k), (∀ v : Fin k → Eucl m, β v = a * γ (Fin.cons w (fun i => T (v i)))) → covectorEuclideanNorm β ≤ |a| * Real.sqrt ((k : ℝ) + 1) * ‖w‖ * ‖T‖ ^ k * covectorEuclideanNorm γ`

## Sibling prerequisites

- `root.integrality_weak_limits-a1.smooth_pushforward-a1.pullback_norm-a1`
- `root.integrality_weak_limits-a1.smooth_pushforward-a1.pullback_norm-a1.tuple_sum_factorial-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
