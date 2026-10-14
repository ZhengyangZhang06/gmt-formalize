# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.integrality_weak_limits-a1.smooth_pushforward-a1.pullback_norm-a1.tuple_sum_factorial-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-smooth-pushforward-a1-pullback-norm-a-71535d6e53/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.integrality_weak_limits-a1.smooth_pushforward-a1.pullback_norm-a1`
- Child key: `tuple_sum_factorial`
- Declaration: `Submission.iwl_sp_pn_sum_sq_tuples_eq_factorial_mul`
- Exact Lean type: `∀ (m j : ℕ) (γ : Covector (Eucl m) j), ∑ i : Fin j → Fin m, (γ (fun k => EuclideanSpace.basisFun (Fin m) ℝ (i k))) ^ 2 = (j.factorial : ℝ) * covectorEuclideanNorm γ ^ 2`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
