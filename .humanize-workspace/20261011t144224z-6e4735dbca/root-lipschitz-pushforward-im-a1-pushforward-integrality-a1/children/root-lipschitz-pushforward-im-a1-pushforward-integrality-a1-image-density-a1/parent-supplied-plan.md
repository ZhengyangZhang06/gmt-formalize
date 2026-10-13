# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.lipschitz_pushforward_im-a1.pushforward_integrality-a1.image_density-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-pushforward-integrality-a1-image-density-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.lipschitz_pushforward_im-a1.pushforward_integrality-a1`
- Child key: `image_density`
- Declaration: `Submission.lpf_pi_image_density`
- Exact Lean type: `∀ (P Q n : ℕ) (V : Set (Eucl Q)) (M : Set (Eucl P)) (θ : Eucl P → ℝ) (Ξ : Eucl P → NVector (Eucl Q) n) (f : Eucl P → Eucl Q) (G : ℕ → Eucl n → Eucl Q) (O : ℕ → Set (Eucl n)) (S : GeometricCurrentOn V n), IsOpen V → NullMeasurableSet M (μHE[n] : Measure (Eucl P)) → (∀ x ∈ M, 0 < θ x) → (∀ x ∈ M, ∃ k : ℕ, θ x = k) → AEMeasurable θ ((μHE[n] : Measure (Eucl P)).restrict M) → AEStronglyMeasurable Ξ ((μHE[n] : Measure (Eucl P)).restrict M) → ContinuousOn f M → MapsTo f M V → (∀ Z ⊆ M, (μHE[n] : Measure (Eucl P)) Z = 0 → (μHE[n] : Measure (Eucl Q)) (f '' Z) = 0) → (∀ (A : Set (Eucl P)) (h : Eucl P → ℝ≥0∞), A ⊆ M → NullMeasurableSet A (μHE[n] : Measure (Eucl P)) → AEMeasurable h ((μHE[n] : Measure (Eucl P)).restrict A) → AEMeasurable (fun y => ∑' x : {x : Eucl P // x ∈ A ∧ f x = y}, h x) (μHE[n] : Measure (Eucl Q)) ∧ ∫⁻ x in A, h x * ‖Ξ x‖ₑ ∂(μHE[n] : Measure (Eucl P)) = ∫⁻ y, ∑' x : {x : Eucl P // x ∈ A ∧ f x = y}, h x ∂(μHE[n] : Measure (Eucl Q))) → (∀ K : Set (Eucl Q), IsCompact K → K ⊆ V → ∫⁻ x in M ∩ f ⁻¹' K, ENNReal.ofReal (θ x) * ‖Ξ x‖ₑ ∂(μHE[n] : Measure (Eucl P)) < ∞) → (∀ᵐ x ∂((μHE[n] : Measure (Eucl P)).restrict M), Ξ x ≠ 0 → ∃ k, ∃ w ∈ O k, G k w = f x ∧ ∃ σ : Fin n → Eucl Q, Orthonormal ℝ σ ∧ Submodule.span ℝ (range σ) = LinearMap.range (fderiv ℝ (G k) w).toLinearMap ∧ (Ξ x = ‖Ξ x‖ • simpleNVector σ ∨ Ξ x = -(‖Ξ x‖ • simpleNVector σ))) → (∀ ω : TestFormOn V n, S ω = ∫ x in M, θ x * Ξ x ((ω : DifferentialForm (Eucl Q) n) (f x)) ∂(μHE[n] : Measure (Eucl P))) → ∃ (Y : Set (Eucl Q)) (Ψ : Eucl Q → NVector (Eucl Q) n), Y ⊆ V ∧ NullMeasurableSet Y (μHE[n] : Measure (Eucl Q)) ∧ (∀ K : Set (Eucl Q), IsCompact K → K ⊆ V → (μHE[n] : Measure (Eucl Q)) (Y ∩ K) < ∞) ∧ AEStronglyMeasurable Ψ ((μHE[n] : Measure (Eucl Q)).restrict Y) ∧ (∀ K : Set (Eucl Q), IsCompact K → K ⊆ V → IntegrableOn (fun y => ‖Ψ y‖) (Y ∩ K) (μHE[n] : Measure (Eucl Q))) ∧ (∀ᵐ y ∂((μHE[n] : Measure (Eucl Q)).restrict Y), ∃ (m : ℕ) (a : Fin m → ℤ) (k : Fin m → ℕ) (w : Fin m → Eucl n) (σ : Fin m → Fin n → Eucl Q), (∀ i, w i ∈ O (k i) ∧ G (k i) (w i) = y ∧ Orthonormal ℝ (σ i) ∧ Submodule.span ℝ (range (σ i)) = LinearMap.range (fderiv ℝ (G (k i)) (w i)).toLinearMap) ∧ Ψ y = ∑ i, (a i : ℝ) • simpleNVector (σ i)) ∧ ∀ ω : TestFormOn V n, S ω = ∫ y in Y, Ψ y ((ω : DifferentialForm (Eucl Q) n) y) ∂(μHE[n] : Measure (Eucl Q))`

## Sibling prerequisites

- `root.lipschitz_pushforward_im-a1.pushforward_integrality-a1.signed_fibre_sum-a1`
- `root.lipschitz_pushforward_im-a1.pushforward_integrality-a1.covector_finite_dimensional-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
