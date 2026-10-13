# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.deformation-a1.im_pushforward_limit-a1.minor_weak_continuity-a1.minor_ibp_smooth-a1.integral_fderiv_zero-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-im-pushforward-limit-a1-minor-weak-continuity-a1-53f5a337eb/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.deformation-a1.im_pushforward_limit-a1.minor_weak_continuity-a1.minor_ibp_smooth-a1`
- Child key: `integral_fderiv_zero`
- Declaration: `Submission.deformation_ipl_mwc_mis_integral_fderiv_eq_zero`
- Exact Lean type: `∀ (k : ℕ) (h : Eucl k → ℝ) (e : Eucl k), ContDiff ℝ 1 h → HasCompactSupport h → ∫ w, fderiv ℝ h w e ∂(volume : Measure (Eucl k)) = 0`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
