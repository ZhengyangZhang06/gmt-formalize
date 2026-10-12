# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.bv_results-a1.extension-a1.weighted_gradient-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-bv-results-a1-extension-a1-weighted-gradient-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.bv_results-a1.extension-a1`
- Child key: `weighted_gradient`
- Declaration: `Submission.bv_ext_lintegral_enorm_mul_fderiv_le`
- Exact Lean type: `∀ (n : ℕ) (U : Set (Rn n)) (ξ : Rn n) (R r : ℝ) (u φ : Rn n → ℝ), IsOpen U → 0 < R → U ⊆ closedBall ξ R → Integrable u volume → (∃ K, LipschitzWith K φ) → (∀ x, 0 ≤ φ x ∧ φ x ≤ 1) → HasCompactSupport φ → tsupport φ ⊆ U → (∀ᵐ x ∂volume, r * ‖fderiv ℝ φ x‖ ≤ -fderiv ℝ φ x (x - ξ)) → ENNReal.ofReal r * ∫⁻ x, ‖u x‖ₑ * ‖fderiv ℝ φ x‖ₑ ≤ ENNReal.ofReal R * Chapter02.bvVariationOn (fun x ↦ |u x|) U + (n : ℝ≥0∞) * ∫⁻ x in U, ‖u x‖ₑ`

## Sibling prerequisites

- `root.bv_results-a1.extension-a1.divergence_smul-a1`
- `root.bv_results-a1.extension-a1.admissible_field-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
