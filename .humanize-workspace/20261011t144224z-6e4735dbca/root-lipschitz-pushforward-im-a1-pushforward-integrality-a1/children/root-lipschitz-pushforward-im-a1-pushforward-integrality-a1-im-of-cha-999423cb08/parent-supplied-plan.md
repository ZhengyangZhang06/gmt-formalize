# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.lipschitz_pushforward_im-a1.pushforward_integrality-a1.im_of_chart_density-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-pushforward-integrality-a1-im-of-cha-999423cb08/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.lipschitz_pushforward_im-a1.pushforward_integrality-a1`
- Child key: `im_of_chart_density`
- Declaration: `Submission.lpf_pi_im_of_chart_density`
- Exact Lean type: `(∀ (Q n : ℕ) (V M : Set (Eucl Q)) (θ : Eucl Q → ℝ) (Φ : Eucl n → Eucl Q) (Ω : Set (Eucl n)), IsOpen V → M ⊆ V → NullMeasurableSet M (μHE[n] : Measure (Eucl Q)) → (∀ y ∈ M, 0 < θ y) → (∀ K : Set (Eucl Q), IsCompact K → K ⊆ V → IntegrableOn θ (M ∩ K) (μHE[n] : Measure (Eucl Q))) → IsOpen Ω → ContDiff ℝ 1 Φ → (∃ c : ℝ, 0 < c ∧ ∀ w ∈ Ω, ∀ w' ∈ Ω, c * ‖w - w'‖ ≤ ‖Φ w - Φ w'‖) → ∀ᵐ y ∂((μHE[n] : Measure (Eucl Q)).restrict (M ∩ Φ '' Ω)), ∀ w ∈ Ω, Φ w = y → HasWeightedApproximateTangentSpaceAt n M θ y (LinearMap.range (fderiv ℝ Φ w).toLinearMap)) → ((∀ (P n : ℕ) (v : Fin n → Eucl P), ‖simpleNVector v‖ ^ 2 = (Matrix.of fun i j => inner ℝ (v i) (v j)).det) ∧ ∀ (P n : ℕ) (B : Matrix (Fin n) (Fin n) ℝ) (τ : Fin n → Eucl P), simpleNVector (fun i => ∑ j, B i j • τ j) = B.det • simpleNVector τ) → ∀ (Q n : ℕ) (V Y : Set (Eucl Q)) (Ψ : Eucl Q → NVector (Eucl Q) n) (G : ℕ → Eucl n → Eucl Q) (O : ℕ → Set (Eucl n)) (S : GeometricCurrentOn V n), IsOpen V → (∀ k, IsOpen (O k)) → (∀ k, ContDiff ℝ 1 (G k)) → (∀ k, ∃ c : ℝ, 0 < c ∧ ∀ w ∈ O k, ∀ w' ∈ O k, c * ‖w - w'‖ ≤ ‖G k w - G k w'‖) → Y ⊆ V → NullMeasurableSet Y (μHE[n] : Measure (Eucl Q)) → (∀ K : Set (Eucl Q), IsCompact K → K ⊆ V → (μHE[n] : Measure (Eucl Q)) (Y ∩ K) < ∞) → AEStronglyMeasurable Ψ ((μHE[n] : Measure (Eucl Q)).restrict Y) → (∀ K : Set (Eucl Q), IsCompact K → K ⊆ V → IntegrableOn (fun y => ‖Ψ y‖) (Y ∩ K) (μHE[n] : Measure (Eucl Q))) → (∀ᵐ y ∂((μHE[n] : Measure (Eucl Q)).restrict Y), ∃ (m : ℕ) (a : Fin m → ℤ) (k : Fin m → ℕ) (w : Fin m → Eucl n) (σ : Fin m → Fin n → Eucl Q), (∀ i, w i ∈ O (k i) ∧ G (k i) (w i) = y ∧ Orthonormal ℝ (σ i) ∧ Submodule.span ℝ (range (σ i)) = LinearMap.range (fderiv ℝ (G (k i)) (w i)).toLinearMap) ∧ Ψ y = ∑ i, (a i : ℝ) • simpleNVector (σ i)) → (∀ ω : TestFormOn V n, S ω = ∫ y in Y, Ψ y ((ω : DifferentialForm (Eucl Q) n) y) ∂(μHE[n] : Measure (Eucl Q))) → IsIntegerMultiplicity S`

## Sibling prerequisites

- `root.lipschitz_pushforward_im-a1.pushforward_integrality-a1.simple_unit_facts-a1`
- `root.lipschitz_pushforward_im-a1.pushforward_integrality-a1.chart_image_rectifiable-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
