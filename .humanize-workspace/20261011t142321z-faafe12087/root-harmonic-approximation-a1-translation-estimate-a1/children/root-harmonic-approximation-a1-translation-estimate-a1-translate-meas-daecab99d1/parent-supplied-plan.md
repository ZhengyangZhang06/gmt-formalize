# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.harmonic_approximation-a1.translation_estimate-a1.translate_measurability-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-harmonic-approximation-a1-translation-estimate-a1-translate-meas-daecab99d1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.harmonic_approximation-a1.translation_estimate-a1`
- Child key: `translate_measurability`
- Declaration: `Submission.aestronglyMeasurable_ball_comp_sub`
- Exact Lean type: `∀ (n : ℕ) (h : Rn n → ℝ) (r s : ℝ) (z : Rn n), r + ‖z‖ ≤ s → AEStronglyMeasurable h (volume.restrict (ball (0 : Rn n) s)) → AEStronglyMeasurable (fun x => h (x - z)) (volume.restrict (ball (0 : Rn n) r))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
