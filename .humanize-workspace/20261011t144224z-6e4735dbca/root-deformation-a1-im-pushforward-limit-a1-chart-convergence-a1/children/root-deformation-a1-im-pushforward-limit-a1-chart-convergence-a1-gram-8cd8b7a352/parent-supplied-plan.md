# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.deformation-a1.im_pushforward_limit-a1.chart_convergence-a1.gram_det_lower_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-im-pushforward-limit-a1-chart-convergence-a1-gram-8cd8b7a352/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.deformation-a1.im_pushforward_limit-a1.chart_convergence-a1`
- Child key: `gram_det_lower_bound`
- Declaration: `Submission.deformation_ipl_cc_gram_det_lower_bound`
- Exact Lean type: `∀ (P k : ℕ) (T : Eucl k →L[ℝ] Eucl P) (c : ℝ), 0 ≤ c → (∀ s : Eucl k, c * ‖s‖ ≤ ‖T s‖) → c ^ k ≤ Real.sqrt (Matrix.of fun i j => inner ℝ (T (EuclideanSpace.single i 1)) (T (EuclideanSpace.single j 1))).det`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
