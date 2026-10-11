# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.bv_results-a1.mollifier_gradient-a1.smooth_duality_compact-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-bv-results-a1-mollifier-gradient-a1-smooth-duality-compact-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.bv_results-a1.mollifier_gradient-a1`
- Child key: `smooth_duality_compact`
- Declaration: `Submission.bv_lintegral_norm_fderiv_le_of_dual_compact`
- Exact Lean type: `∀ (n : ℕ) (w : Rn n → ℝ) (O L : Set (Rn n)) (M : ℝ≥0∞), ContDiff ℝ 2 w → IsOpen O → IsCompact L → L ⊆ O → (∀ g : Rn n → Rn n, ContDiff ℝ 1 g → HasCompactSupport g → tsupport g ⊆ O → (∀ x, ‖g x‖ ≤ 1) → ENNReal.ofReal (-∫ x, fderiv ℝ w x (g x)) ≤ M) → ∫⁻ x in L, ‖fderiv ℝ w x‖ₑ ≤ M`

## Sibling prerequisites

- `root.bv_results-a1.mollifier_gradient-a1.smooth_cutoff-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
