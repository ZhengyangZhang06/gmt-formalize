# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.deformation-a1.im_pushforward_limit-a1.minor_weak_continuity-a1.piola_identity-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-im-pushforward-limit-a1-minor-weak-continuity-a1-f2e89eb27d/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.deformation-a1.im_pushforward_limit-a1.minor_weak_continuity-a1`
- Child key: `piola_identity`
- Declaration: `Submission.deformation_ipl_mwc_piola_identity`
- Exact Lean type: `∀ (k r : ℕ) (W : Fin r → Eucl k → ℝ) (b : Fin (r + 1) → Fin k), (∀ t, ContDiff ℝ 2 (W t)) → ∀ w : Eucl k, ∑ q : Fin (r + 1), fderiv ℝ (fun x : Eucl k => (-1 : ℝ) ^ (q : ℕ) * Matrix.det (Matrix.of fun t s : Fin r => fderiv ℝ (W t) x (EuclideanSpace.single (b (q.succAbove s)) 1))) w (EuclideanSpace.single (b q) 1) = 0`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
