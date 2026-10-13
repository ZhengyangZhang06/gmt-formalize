# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.deformation-a1.im_pushforward_limit-a1.minor_weak_continuity-a1.minor_ibp_smooth-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-im-pushforward-limit-a1-minor-weak-continuity-a1-327766afed/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.deformation-a1.im_pushforward_limit-a1.minor_weak_continuity-a1`
- Child key: `minor_ibp_smooth`
- Declaration: `Submission.deformation_ipl_mwc_minor_ibp_smooth`
- Exact Lean type: `∀ (k r : ℕ) (V : Fin (r + 1) → Eucl k → ℝ) (b : Fin (r + 1) → Fin k) (φ : Eucl k → ℝ), (∀ t, ContDiff ℝ 2 (V t)) → ContDiff ℝ 1 φ → HasCompactSupport φ → ∫ w, φ w * Matrix.det (Matrix.of fun t s : Fin (r + 1) => fderiv ℝ (V t) w (EuclideanSpace.single (b s) 1)) ∂(volume : Measure (Eucl k)) = -∑ q : Fin (r + 1), ∫ w, V 0 w * ((-1 : ℝ) ^ (q : ℕ) * Matrix.det (Matrix.of fun t s : Fin r => fderiv ℝ (V t.succ) w (EuclideanSpace.single (b (q.succAbove s)) 1))) * fderiv ℝ φ w (EuclideanSpace.single (b q) 1) ∂(volume : Measure (Eucl k))`

## Sibling prerequisites

- `root.deformation-a1.im_pushforward_limit-a1.minor_weak_continuity-a1.piola_identity-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
