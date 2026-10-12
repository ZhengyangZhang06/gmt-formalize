# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.bv_results-a1.extension-a1.localized_pairing-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-bv-results-a1-extension-a1-localized-pairing-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.bv_results-a1.extension-a1`
- Child key: `localized_pairing`
- Declaration: `Submission.bv_ext_ofReal_integral_cutoff_le`
- Exact Lean type: `∀ (n : ℕ) (U : Set (Rn n)) (u φ : Rn n → ℝ) (g : CompactlySupportedContinuousMap (Rn n) (Rn n)), IsOpen U → Integrable u volume → (∃ K, LipschitzWith K φ) → (∀ x, 0 ≤ φ x ∧ φ x ≤ 1) → HasCompactSupport φ → tsupport φ ⊆ U → Chapter02.IsLipschitzTestField g → Chapter02.compactlySupportedSupNorm g ≤ 1 → ENNReal.ofReal (∫ x, φ x * u x * Chapter02.euclideanDivergence (g : Rn n → Rn n) x) ≤ Chapter02.bvVariationOn u U + ∫⁻ x, ‖u x‖ₑ * ‖fderiv ℝ φ x‖ₑ`

## Sibling prerequisites

- `root.bv_results-a1.extension-a1.divergence_smul-a1`
- `root.bv_results-a1.extension-a1.admissible_field-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
