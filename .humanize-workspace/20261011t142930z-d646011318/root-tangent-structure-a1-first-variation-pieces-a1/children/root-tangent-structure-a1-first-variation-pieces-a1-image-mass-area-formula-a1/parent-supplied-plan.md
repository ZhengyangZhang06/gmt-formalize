# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.tangent_structure-a1.first_variation_pieces-a1.image_mass_area_formula-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-tangent-structure-a1-first-variation-pieces-a1-image-mass-area-formula-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.tangent_structure-a1.first_variation_pieces-a1`
- Child key: `image_mass_area_formula`
- Declaration: `Submission.ts_fv_image_mass_area_formula`
- Exact Lean type: `∀ (n ℓ : ℕ) (a : RectifiablePair n ℓ) (N₀ : Set (Ambient n ℓ)) (C : ℕ → Set (EuclideanSpace ℝ (Fin n))) (F : ℕ → EuclideanSpace ℝ (Fin n) → Ambient n ℓ) (f : Ambient n ℓ → Ambient n ℓ) (K : Set (Ambient n ℓ)), 0 < n → MeasurableSet N₀ → (μHE[n] : Measure (Ambient n ℓ)) N₀ = 0 → a.M ⊆ N₀ ∪ ⋃ i, F i '' C i → (∀ i, IsCompact (C i) ∧ (∃ K : NNReal, LipschitzWith K (F i)) ∧ (∀ w ∈ C i, DifferentiableAt ℝ (F i) w ∧ Function.Injective (fderiv ℝ (F i) w)) ∧ ContinuousOn (fderiv ℝ (F i)) (C i) ∧ ∃ c : ℝ, 0 < c ∧ ∀ v ∈ C i, ∀ w ∈ C i, c * ‖v - w‖ ≤ ‖F i v - F i w‖) → (∀ᵐ x ∂(μHE[n] : Measure (Ambient n ℓ)).restrict a.M, ∀ i, ∀ w ∈ C i, F i w = x → (mk a).tangentSpace x = LinearMap.range (fderiv ℝ (F i) w).toLinearMap) → Function.Injective f → (∃ L : NNReal, LipschitzWith L f) → (∀ y, DifferentiableAt ℝ f y) → MeasurableSet K → imageMass a f K = ∫⁻ x in a.M ∩ K, ENNReal.ofReal (a.θ x * Real.sqrt (Matrix.det (Matrix.of fun i j : Fin (n + ℓ) ↦ inner ℝ (fderiv ℝ f x (((mk a).tangentSpace x).starProjection (EuclideanSpace.single i (1 : ℝ)))) (fderiv ℝ f x (((mk a).tangentSpace x).starProjection (EuclideanSpace.single j (1 : ℝ)))) + inner ℝ (EuclideanSpace.single i (1 : ℝ) - ((mk a).tangentSpace x).starProjection (EuclideanSpace.single i (1 : ℝ))) (EuclideanSpace.single j (1 : ℝ) - ((mk a).tangentSpace x).starProjection (EuclideanSpace.single j (1 : ℝ)))))) ∂μHE[n]`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
