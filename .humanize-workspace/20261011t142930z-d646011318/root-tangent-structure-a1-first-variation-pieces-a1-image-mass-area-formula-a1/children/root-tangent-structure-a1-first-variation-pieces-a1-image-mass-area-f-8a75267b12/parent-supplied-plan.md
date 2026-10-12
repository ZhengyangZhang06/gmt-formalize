# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.tangent_structure-a1.first_variation_pieces-a1.image_mass_area_formula-a1.piece_image_area_formula-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-tangent-structure-a1-first-variation-pieces-a1-image-mass-area-f-8a75267b12/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.tangent_structure-a1.first_variation_pieces-a1.image_mass_area_formula-a1`
- Child key: `piece_image_area_formula`
- Declaration: `Submission.ts_fv_piece_image_area_formula`
- Exact Lean type: `∀ (n ℓ : ℕ) (C : Set (EuclideanSpace ℝ (Fin n))) (F : EuclideanSpace ℝ (Fin n) → Ambient n ℓ) (f : Ambient n ℓ → Ambient n ℓ) (A : Set (Ambient n ℓ)) (P : Ambient n ℓ → Submodule ℝ (Ambient n ℓ)) (w : Ambient n ℓ → ℝ≥0∞), MeasurableSet C → (∃ L : NNReal, LipschitzWith L F) → (∀ v ∈ C, DifferentiableAt ℝ F v) → Set.InjOn F C → (∃ L : NNReal, LipschitzWith L f) → Set.InjOn f A → (∀ y ∈ A, DifferentiableAt ℝ f y) → MeasurableSet A → A ⊆ F '' C → (∀ v ∈ C, F v ∈ A → P (F v) = LinearMap.range (fderiv ℝ F v).toLinearMap) → ∫⁻ y in f '' A, w y ∂μHE[n] = ∫⁻ y in A, ENNReal.ofReal (Real.sqrt (Matrix.det (Matrix.of fun i j : Fin (n + ℓ) ↦ inner ℝ (fderiv ℝ f y ((P y).starProjection (EuclideanSpace.single i (1 : ℝ)))) (fderiv ℝ f y ((P y).starProjection (EuclideanSpace.single j (1 : ℝ)))) + inner ℝ (EuclideanSpace.single i (1 : ℝ) - (P y).starProjection (EuclideanSpace.single i (1 : ℝ))) (EuclideanSpace.single j (1 : ℝ) - (P y).starProjection (EuclideanSpace.single j (1 : ℝ)))))) * w (f y) ∂μHE[n]`

## Sibling prerequisites

- `root.tangent_structure-a1.first_variation_pieces-a1.image_mass_area_formula-a1.det_tangential_gram-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
