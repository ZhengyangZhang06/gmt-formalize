# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.allard_any_radius-a1.graph_rate-a1.la_basics-a1.hs_norm-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-any-radius-a1-graph-rate-a1-la-basics-a1-hs-norm-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.allard_any_radius-a1.graph_rate-a1.la_basics-a1`
- Child key: `hs_norm`
- Declaration: `Submission.any_radius_gr_la_hsNorm_facts`
- Exact Lean type: `(∀ (m k : ℕ) (M N : Rn m →L[ℝ] Rn k), 0 ≤ hsNormSq M ∧ hsNorm M ^ 2 = hsNormSq M ∧ hsNormSq (M + N) ≤ 2 * hsNormSq M + 2 * hsNormSq N ∧ hsNormSq (-M) = hsNormSq M ∧ (hsNormSq M = 0 → M = 0) ∧ ‖M‖ ≤ hsNorm M ∧ hsNorm M ≤ Real.sqrt m * ‖M‖) ∧ ∀ (m : ℕ) (K : Submodule ℝ (Rn m)), hsNormSq K.starProjection ≤ m`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
