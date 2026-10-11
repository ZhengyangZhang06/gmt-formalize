# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.bv_results-a1.mollifier_estimate-a1.smooth_translation-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-bv-results-a1-mollifier-estimate-a1-smooth-translation-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.bv_results-a1.mollifier_estimate-a1`
- Child key: `smooth_translation`
- Declaration: `Submission.bv_translate_sub_lintegral_le_of_fderiv`
- Exact Lean type: `∀ (n : ℕ) (w : Rn n → ℝ) (Q : Set (Rn n)) (z : Rn n) (M : ℝ≥0∞), ContDiff ℝ 1 w → (∀ s ∈ Icc (0 : ℝ) 1, ∫⁻ y in (fun x ↦ x - s • z) '' Q, ‖fderiv ℝ w y‖ₑ ≤ M) → ∫⁻ x in Q, ‖w (x - z) - w x‖ₑ ≤ ENNReal.ofReal ‖z‖ * M`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
