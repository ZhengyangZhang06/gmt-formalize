# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.sobolev_inequality-a1.truncation_layer_cake-a1.level_integral_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-sobolev-inequality-a1-truncation-layer-cake-a1-level-integral-bound-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.sobolev_inequality-a1.truncation_layer_cake-a1`
- Child key: `level_integral_bound`
- Declaration: `Submission.sobolev_level_integral_bound`
- Exact Lean type: `∀ (n ℓ : ℕ) (μ : Measure (Ambient n ℓ)) (h D K : Ambient n ℓ → ℝ) (γ : ℝ → ℝ) (C ε : ℝ), 2 ≤ n → IsFiniteMeasureOnCompacts μ → Continuous h → HasCompactSupport h → (∀ x, 0 ≤ h x) → (∀ x, 0 ≤ D x) → Integrable D μ → (∀ x, 0 ≤ K x) → IntegrableOn K (tsupport h) μ → ContDiff ℝ 1 γ → Monotone γ → (∀ s, 0 ≤ γ s ∧ γ s ≤ 1) → (∀ s, s ≤ 0 → γ s = 0) → 0 ≤ C → 0 < ε → (∀ t : ℝ, 0 ≤ t → μ.real {x | t + ε < h x} ≤ C * (μ.real {x | t < h x}) ^ (n : ℝ)⁻¹ * ((∫ x, deriv γ (h x - t) * D x ∂μ) + ∫ x in {x | t < h x}, K x ∂μ)) → ((n : ℝ) - 1) / n * ∫ x in {x | ε < h x}, (h x ^ ((n : ℝ) / ((n : ℝ) - 1)) - ε ^ ((n : ℝ) / ((n : ℝ) - 1))) ∂μ ≤ C * (∫ x in {x | 0 < h x}, (h x + ε) ^ ((n : ℝ) / ((n : ℝ) - 1)) ∂μ) ^ (n : ℝ)⁻¹ * ∫ x, (D x + h x * K x) ∂μ`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
