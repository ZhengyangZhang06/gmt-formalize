# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.harmonic_approximation-a1.translation_estimate-a1.ball_translate_lintegral-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-harmonic-approximation-a1-translation-estimate-a1-ball-translate-fb82697a57/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.harmonic_approximation-a1.translation_estimate-a1`
- Child key: `ball_translate_lintegral`
- Declaration: `Submission.lintegral_ball_comp_sub_le`
- Exact Lean type: `∀ (n : ℕ) (F : Rn n → ℝ≥0∞) (r s : ℝ) (w : Rn n), r + ‖w‖ ≤ s → ∫⁻ x in ball (0 : Rn n) r, F (x - w) ≤ ∫⁻ x in ball (0 : Rn n) s, F x`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
