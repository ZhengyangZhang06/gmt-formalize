# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.variation_formulas-a1.image_area_formula-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-variation-formulas-a1-image-area-formula-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.variation_formulas-a1`
- Child key: `image_area_formula`
- Declaration: `Submission.variation_submanifold_image_area`
- Exact Lean type: `∀ (n N N' : ℕ) (M S : Set (Rn N)) (f : Rn N → Rn N'), Chapter02.IsSimonSubmanifold (E := Rn n) 1 M → (∀ (V : Set (Rn n)) (W : Set (Rn N)) (ψ : Rn n → Rn N), Chapter02.IsSimonLocalRepresentation 1 M V W ψ → ∀ x ∈ V, tangentSpace M (ψ x) = LinearMap.range (fderiv ℝ ψ x).toLinearMap) → MeasurableSet S → S ⊆ M → (∀ y ∈ S, DifferentiableAt ℝ f y) → (∀ y ∈ S, Function.Injective (fderiv ℝ f y)) → InjOn f S → μHE[n] (f '' S) = ∫⁻ y in S, ENNReal.ofReal (areaJacobian ((fderiv ℝ f y).comp (tangentSpace M y).subtypeL)) ∂μHE[n]`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
