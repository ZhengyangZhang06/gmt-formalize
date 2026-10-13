# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.harmonic_approximation-a1.poincare_inequality-a1.exhaustion-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-harmonic-approximation-a1-poincare-inequality-a1-exhaustion-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.harmonic_approximation-a1.poincare_inequality-a1`
- Child key: `exhaustion`
- Declaration: `Submission.poincare_ball_double_integral_exhaustion`
- Exact Lean type: `∀ (n : ℕ) (f : Rn n → ℝ) (K : ℝ≥0∞), AEStronglyMeasurable f (volume.restrict (ball (0 : Rn n) 1)) → (∀ r : ℝ, 0 < r → r < 1 → ∫⁻ x in ball (0 : Rn n) r, ∫⁻ y in ball (0 : Rn n) r, ‖f x - f y‖ₑ ^ 2 ≤ K) → ∫⁻ x in ball (0 : Rn n) 1, ∫⁻ y in ball (0 : Rn n) 1, ‖f x - f y‖ₑ ^ 2 ≤ K`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
