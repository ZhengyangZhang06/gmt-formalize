# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.sobolev_inequality-a1.truncation_layer_cake-a1.level_integral_bound-a1.layer_cake-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-sobolev-inequality-a1-truncation-layer-cake-a1-level-integral-bo-4e69efe26e/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.sobolev_inequality-a1.truncation_layer_cake-a1.level_integral_bound-a1`
- Child key: `layer_cake`
- Declaration: `Submission.sobolev_level_layer_cake`
- Exact Lean type: `∀ (n ℓ : ℕ) (μ : Measure (Ambient n ℓ)) (h : Ambient n ℓ → ℝ) (ε : ℝ), 2 ≤ n → IsFiniteMeasureOnCompacts μ → Continuous h → HasCompactSupport h → (∀ x, 0 ≤ h x) → 0 < ε → ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal ((t + ε) ^ ((n : ℝ) - 1)⁻¹ * μ.real {x | t + ε < h x}) = ENNReal.ofReal (((n : ℝ) - 1) / n * ∫ x in {x | ε < h x}, (h x ^ ((n : ℝ) / ((n : ℝ) - 1)) - ε ^ ((n : ℝ) / ((n : ℝ) - 1))) ∂μ)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
