# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.harmonic_approximation-a1.translation_estimate-a1.smooth_translation_estimate-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-harmonic-approximation-a1-translation-estimate-a1-smooth-transla-8e4183bc7d/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.harmonic_approximation-a1.translation_estimate-a1`
- Child key: `smooth_translation_estimate`
- Declaration: `Submission.contDiff_one_ball_translation_estimate`
- Exact Lean type: `∀ (n : ℕ) (φ : Rn n → ℝ), ContDiff ℝ 1 φ → ∀ (r : ℝ) (z : Rn n), ∫⁻ x in ball (0 : Rn n) r, ‖φ (x - z) - φ x‖ₑ ^ 2 ≤ ENNReal.ofReal (‖z‖ ^ 2) * ∫⁻ x in ball (0 : Rn n) (r + ‖z‖), ‖gradient φ x‖ₑ ^ 2`

## Sibling prerequisites

- `root.harmonic_approximation-a1.translation_estimate-a1.ball_translate_lintegral-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
