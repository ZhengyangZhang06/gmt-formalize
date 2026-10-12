# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.tangent_structure-a1.first_variation_pieces-a1.image_mass_area_formula-a1.image_lintegral_gluing-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-tangent-structure-a1-first-variation-pieces-a1-image-mass-area-f-a5f97e29ab/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.tangent_structure-a1.first_variation_pieces-a1.image_mass_area_formula-a1`
- Child key: `image_lintegral_gluing`
- Declaration: `Submission.ts_fv_lintegral_image_eq_of_pieces`
- Exact Lean type: `∀ (X : Type) [MeasurableSpace X] (μ : Measure X) (f : X → X) (Z : Set X) (D : ℕ → Set X) (u g : X → ℝ≥0∞), Function.Injective f → (∀ Y : Set X, μ Y = 0 → μ (f '' Y) = 0) → (∀ Y : Set X, NullMeasurableSet Y μ → NullMeasurableSet (f '' Y) μ) → NullMeasurableSet Z μ → (∀ i, MeasurableSet (D i)) → Pairwise (fun i j ↦ Disjoint (D i) (D j)) → μ (Z \ ⋃ i, D i) = 0 → (∀ i, ∫⁻ y in f '' (Z ∩ D i), u y ∂μ = ∫⁻ x in Z ∩ D i, g x ∂μ) → ∫⁻ y in f '' Z, u y ∂μ = ∫⁻ x in Z, g x ∂μ`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
