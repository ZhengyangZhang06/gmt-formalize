# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.poincare_inequality-a1.layer_cake_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-poincare-inequality-a1-layer-cake-bound-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.poincare_inequality-a1`
- Child key: `layer_cake_bound`
- Declaration: `Submission.layer_cake_tonelli_truncation_bound`
- Exact Lean type: `∀ {X : Type} [MeasurableSpace X] (μ : Measure X) [SFinite μ] (A B : Set X) (h : X → ℝ) (φ : ℝ → X → ℝ≥0∞) (G : X → ℝ≥0∞) (k : X → X → ℝ≥0∞) (κ L : ℝ≥0∞) (ε : ℝ), MeasurableSet A → MeasurableSet B → Measurable h → Measurable (Function.uncurry φ) → Measurable G → Measurable (Function.uncurry k) → (∀ x ∈ B, ∫⁻ t in Ioi 0, φ t x ≤ 1) → (∀ x ∈ B, ∫⁻ ζ in A, k x ζ ∂μ ≤ L) → (∀ t : ℝ, 0 < t → ∀ᵐ ζ ∂μ, ζ ∈ A → t + ε < h ζ → κ ≤ ∫⁻ x in B, φ t x * G x * k x ζ ∂μ) → κ * ∫⁻ ζ in A, ENNReal.ofReal (h ζ - ε) ∂μ ≤ L * ∫⁻ x in B, G x ∂μ`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
