# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.bv_results-a1.extension-a1.admissible_field-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-bv-results-a1-extension-a1-admissible-field-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.bv_results-a1.extension-a1`
- Child key: `admissible_field`
- Declaration: `Submission.bv_ext_ofReal_integral_le_bvVariationOn`
- Exact Lean type: `∀ (n : ℕ) (W : Set (Rn n)) (v : Rn n → ℝ) (G : Rn n → Rn n) (K : ℝ≥0), LipschitzWith K G → HasCompactSupport G → tsupport G ⊆ W → (∀ x, ‖G x‖ ≤ 1) → ENNReal.ofReal (∫ x in W, v x * Chapter02.euclideanDivergence G x) ≤ Chapter02.bvVariationOn v W`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
