# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.variation_formulas-a1.image_area_formula-a1.chart_image_area-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-variation-formulas-a1-image-area-formula-a1-chart-image-area-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.variation_formulas-a1.image_area_formula-a1`
- Child key: `chart_image_area`
- Declaration: `Submission.variation_chart_image_area`
- Exact Lean type: `∀ (n N N' : ℕ) (M : Set (Rn N)) (V : Set (Rn n)) (W : Set (Rn N)) (ψ : Rn n → Rn N) (f : Rn N → Rn N') (B : Set (Rn N)), Chapter02.IsSimonLocalRepresentation 1 M V W ψ → (∀ x ∈ V, tangentSpace M (ψ x) = LinearMap.range (fderiv ℝ ψ x).toLinearMap) → MeasurableSet B → B ⊆ W ∩ M → (∀ y ∈ B, DifferentiableAt ℝ f y) → (∀ y ∈ B, Function.Injective (fderiv ℝ f y)) → InjOn f B → μHE[n] (f '' B) = ∫⁻ y in B, ENNReal.ofReal (areaJacobian ((fderiv ℝ f y).comp (tangentSpace M y).subtypeL)) ∂μHE[n]`

## Sibling prerequisites

- `root.variation_formulas-a1.image_area_formula-a1.jacobian_chain_rule-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
