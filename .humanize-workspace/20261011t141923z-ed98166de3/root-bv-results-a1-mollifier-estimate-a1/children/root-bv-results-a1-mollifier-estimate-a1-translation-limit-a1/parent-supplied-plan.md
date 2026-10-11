# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.bv_results-a1.mollifier_estimate-a1.translation_limit-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-bv-results-a1-mollifier-estimate-a1-translation-limit-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.bv_results-a1.mollifier_estimate-a1`
- Child key: `translation_limit`
- Declaration: `Submission.bv_translate_sub_lintegral_le_of_tendsto`
- Exact Lean type: `∀ (n : ℕ) (F : Rn n → ℝ) (w : ℕ → Rn n → ℝ) (Q : Set (Rn n)) (z : Rn n) (C : ℝ≥0∞), AEStronglyMeasurable F volume → (∀ j, AEStronglyMeasurable (w j) volume) → Tendsto (fun j ↦ ∫⁻ x, ‖w j x - F x‖ₑ) atTop (𝓝 0) → (∀ j, ∫⁻ x in Q, ‖w j (x - z) - w j x‖ₑ ≤ C) → ∫⁻ x in Q, ‖F (x - z) - F x‖ₑ ≤ C`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
