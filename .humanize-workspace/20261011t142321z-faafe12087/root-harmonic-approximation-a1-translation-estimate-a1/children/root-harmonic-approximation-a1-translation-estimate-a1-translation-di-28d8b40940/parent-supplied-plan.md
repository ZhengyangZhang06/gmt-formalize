# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.harmonic_approximation-a1.translation_estimate-a1.translation_difference_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-harmonic-approximation-a1-translation-estimate-a1-translation-di-28d8b40940/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.harmonic_approximation-a1.translation_estimate-a1`
- Child key: `translation_difference_bound`
- Declaration: `Submission.lintegral_ball_translation_difference_le`
- Exact Lean type: `∀ (n : ℕ) (h : Rn n → ℝ) (r s : ℝ) (z : Rn n), r + ‖z‖ ≤ s → AEStronglyMeasurable h (volume.restrict (ball (0 : Rn n) s)) → ∫⁻ x in ball (0 : Rn n) r, ‖h (x - z) - h x‖ₑ ^ 2 ≤ 4 * ∫⁻ x in ball (0 : Rn n) s, ‖h x‖ₑ ^ 2`

## Sibling prerequisites

- `root.harmonic_approximation-a1.translation_estimate-a1.ball_translate_lintegral-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
