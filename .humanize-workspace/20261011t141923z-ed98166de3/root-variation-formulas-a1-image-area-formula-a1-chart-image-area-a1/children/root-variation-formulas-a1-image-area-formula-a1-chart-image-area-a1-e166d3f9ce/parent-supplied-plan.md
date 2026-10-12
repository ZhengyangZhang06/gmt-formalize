# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.variation_formulas-a1.image_area_formula-a1.chart_image_area-a1.injective_area_formula-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-variation-formulas-a1-image-area-formula-a1-chart-image-area-a1-e166d3f9ce/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.variation_formulas-a1.image_area_formula-a1.chart_image_area-a1`
- Child key: `injective_area_formula`
- Declaration: `Submission.variation_injective_area_formula`
- Exact Lean type: `∀ (n N : ℕ) (s : Set (Rn n)) (Φ : Rn n → Rn N), MeasurableSet s → (∀ x ∈ s, DifferentiableAt ℝ Φ x) → (∀ x ∈ s, Function.Injective (fderiv ℝ Φ x)) → InjOn Φ s → μHE[n] (Φ '' s) = ∫⁻ x in s, ENNReal.ofReal (areaJacobian (fderiv ℝ Φ x)) ∂μHE[n]`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
