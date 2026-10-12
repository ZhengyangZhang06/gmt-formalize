# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.harmonic_approximation-a1.poincare_inequality-a1.segment_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-harmonic-approximation-a1-poincare-inequality-a1-segment-bound-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.harmonic_approximation-a1.poincare_inequality-a1`
- Child key: `segment_bound`
- Declaration: `Submission.poincare_c1_segment_sq_bound`
- Exact Lean type: `∀ (n : ℕ) (φ : Rn n → ℝ), ContDiff ℝ 1 φ → ∀ x y : Rn n, ‖φ x - φ y‖ₑ ^ 2 ≤ ‖x - y‖ₑ ^ 2 * ∫⁻ t in Icc (0 : ℝ) 1, ‖gradient φ ((1 - t) • y + t • x)‖ₑ ^ 2`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
