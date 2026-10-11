# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.harmonic_approximation-a1.translation_estimate-a1.l2_limit_closure-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-harmonic-approximation-a1-translation-estimate-a1-l2-limit-closure-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.harmonic_approximation-a1.translation_estimate-a1`
- Child key: `l2_limit_closure`
- Declaration: `Submission.lintegral_sq_le_of_l2_approximation`
- Exact Lean type: `∀ {α E F : Type} [MeasurableSpace α] [NormedAddCommGroup E] [NormedAddCommGroup F] (μ ν : Measure α) (c : ℝ≥0∞) (a : ℕ → α → E) (a₀ : α → E) (b : ℕ → α → F) (b₀ : α → F), c ≠ ∞ → (∀ j, AEStronglyMeasurable (a j) μ) → AEStronglyMeasurable a₀ μ → (∀ j, AEStronglyMeasurable (b j) ν) → AEStronglyMeasurable b₀ ν → Tendsto (fun j => ∫⁻ x, ‖a j x - a₀ x‖ₑ ^ 2 ∂μ) atTop (𝓝 0) → Tendsto (fun j => ∫⁻ x, ‖b j x - b₀ x‖ₑ ^ 2 ∂ν) atTop (𝓝 0) → (∀ j, ∫⁻ x, ‖a j x‖ₑ ^ 2 ∂μ ≤ c * ∫⁻ x, ‖b j x‖ₑ ^ 2 ∂ν) → ∫⁻ x, ‖a₀ x‖ₑ ^ 2 ∂μ ≤ c * ∫⁻ x, ‖b₀ x‖ₑ ^ 2 ∂ν`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
