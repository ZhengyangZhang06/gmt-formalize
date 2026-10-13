# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.regular_set_open_dense-a1.rectifiable_c1_cover-a1.c1_approx_ball-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-regular-set-open-dense-a1-rectifiable-c1-cover-a1-c1-approx-ball-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.regular_set_open_dense-a1.rectifiable_c1_cover-a1`
- Child key: `c1_approx_ball`
- Declaration: `Submission.rsod_lipschitz_c1_approx_closedBall`
- Exact Lean type: `∀ (n : ℕ) (f : Rn n → ℝ) (K : ℝ≥0), LipschitzWith K f → ∀ (R : ℝ) (ε : ℝ≥0∞), 0 < ε → ∃ g : Rn n → ℝ, ContDiff ℝ 1 g ∧ volume (closedBall (0 : Rn n) R ∩ {x | f x ≠ g x}) < ε`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
