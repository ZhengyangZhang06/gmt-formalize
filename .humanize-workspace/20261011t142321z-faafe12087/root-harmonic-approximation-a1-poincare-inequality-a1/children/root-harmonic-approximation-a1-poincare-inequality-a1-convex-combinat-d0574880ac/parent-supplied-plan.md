# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.harmonic_approximation-a1.poincare_inequality-a1.convex_combination_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-harmonic-approximation-a1-poincare-inequality-a1-convex-combinat-d0574880ac/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.harmonic_approximation-a1.poincare_inequality-a1`
- Child key: `convex_combination_bound`
- Declaration: `Submission.poincare_ball_convex_combination_bound`
- Exact Lean type: `∀ (n : ℕ) (h : Rn n → ℝ≥0∞), Measurable h → ∀ r t : ℝ, 0 < r → 0 ≤ t → t ≤ 1 → ∫⁻ x in ball (0 : Rn n) r, ∫⁻ y in ball (0 : Rn n) r, h ((1 - t) • y + t • x) ≤ (2 : ℝ≥0∞) ^ n * volume (ball (0 : Rn n) r) * ∫⁻ z in ball (0 : Rn n) r, h z`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
