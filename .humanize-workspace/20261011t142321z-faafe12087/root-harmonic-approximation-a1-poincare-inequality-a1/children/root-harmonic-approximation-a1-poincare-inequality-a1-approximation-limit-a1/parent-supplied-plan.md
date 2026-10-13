# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.harmonic_approximation-a1.poincare_inequality-a1.approximation_limit-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-harmonic-approximation-a1-poincare-inequality-a1-approximation-limit-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.harmonic_approximation-a1.poincare_inequality-a1`
- Child key: `approximation_limit`
- Declaration: `Submission.poincare_approx_ball_double_integral_bound`
- Exact Lean type: `∀ (n : ℕ) (f : Rn n → ℝ) (g : Rn n → Rn n) (φ : ℕ → Rn n → ℝ) (r : ℝ), 0 < r → r ≤ 1 → AEStronglyMeasurable f (volume.restrict (ball (0 : Rn n) r)) → AEStronglyMeasurable g (volume.restrict (ball (0 : Rn n) r)) → (∀ j, ContDiff ℝ 1 (φ j)) → Tendsto (fun j => ∫⁻ x in ball (0 : Rn n) r, ‖φ j x - f x‖ₑ ^ 2) atTop (𝓝 0) → Tendsto (fun j => ∫⁻ x in ball (0 : Rn n) r, ‖gradient (φ j) x - g x‖ₑ ^ 2) atTop (𝓝 0) → ∫⁻ x in ball (0 : Rn n) r, ∫⁻ y in ball (0 : Rn n) r, ‖f x - f y‖ₑ ^ 2 ≤ (2 : ℝ≥0∞) ^ (n + 2) * volume (ball (0 : Rn n) 1) * ∫⁻ x in ball (0 : Rn n) r, ‖g x‖ₑ ^ 2`

## Sibling prerequisites

- `root.harmonic_approximation-a1.poincare_inequality-a1.smooth_estimate-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
