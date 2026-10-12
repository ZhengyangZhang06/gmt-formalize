# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.regular_set_open_dense-a1.rectifiable_c1_cover-a1.immersion_ball_chart-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-regular-set-open-dense-a1-rectifiable-c1-cover-a1-immersion-ball-chart-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.regular_set_open_dense-a1.rectifiable_c1_cover-a1`
- Child key: `immersion_ball_chart`
- Declaration: `Submission.rsod_c1_immersion_ball_isC1Submanifold`
- Exact Lean type: `∀ (n ℓ : ℕ) (G : Rn n → Amb n ℓ) (a : Rn n), ContDiff ℝ 1 G → Function.Injective (fderiv ℝ G a) → ∃ σ : ℝ, 0 < σ ∧ IsC1Submanifold n (G '' ball a σ) ∧ (μHE[n] : Measure (Amb n ℓ)) (G '' ball a σ) < ∞`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
