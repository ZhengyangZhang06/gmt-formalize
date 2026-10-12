# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.coarea_and_slices-a1.chart_piece_coarea-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-coarea-and-slices-a1-chart-piece-coarea-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.coarea_and_slices-a1`
- Child key: `chart_piece_coarea`
- Declaration: `Submission.chart_piece_coarea_formula`
- Exact Lean type: `(∀ (n ℓ p : ℕ) (M U : Set (Rn (n + ℓ))) (θ : Rn (n + ℓ) → ℝ) (f : Rn (n + ℓ) → Rn p) (V : Set (Rn n)) (ψ : Rn n → Rn (n + ℓ)), NullMeasurableSet M μHE[n] → IsPositiveLocallyIntegrableWeight n M θ → IsOpen U → M ⊆ U → LocallyLipschitzOn U f → IsOpen V → ContDiffOn ℝ 1 ψ V → (∀ u ∈ V, Function.Injective (fderiv ℝ ψ u)) → ∀ᵐ u ∂(volume : Measure (Rn n)), u ∈ V → ψ u ∈ M → HasWeightedApproximateTangentSpaceAt n M θ (ψ u) (LinearMap.range (fderiv ℝ ψ u).toLinearMap) ∧ DifferentiableAt ℝ (f ∘ ψ) u ∧ ∀ w : Rn n, HasLineDerivAt ℝ f (fderiv ℝ (f ∘ ψ) u w) (ψ u) (fderiv ℝ ψ u w)) → ∀ (m k ℓ : ℕ) (M U : Set (Rn (m + k + ℓ))) (θ : Rn (m + k + ℓ) → ℝ) (f : Rn (m + k + ℓ) → Rn m) (D E : Set (Rn (m + k))) (ψ : Rn (m + k) → Rn (m + k + ℓ)) (G : Rn (m + k) → Rn m), 0 < k → NullMeasurableSet M μHE[m + k] → IsPositiveLocallyIntegrableWeight (m + k) M θ → IsOpen U → M ⊆ U → LocallyLipschitzOn U f → IsOpen D → ContDiffOn ℝ 1 ψ D → InjOn ψ D → (∃ K, LipschitzOnWith K ψ D) → (∀ u ∈ D, Function.Injective (fderiv ℝ ψ u)) → ContDiff ℝ 1 G → MeasurableSet E → E ⊆ D → (∀ u ∈ E, f (ψ u) = G u ∧ HasFDerivAt (f ∘ ψ) (fderiv ℝ G u) u) → ∀ B ⊆ ψ '' E ∩ M, MeasurableSet B → ∀ φ : Rn (m + k + ℓ) → ℝ≥0∞, Measurable φ → AEMeasurable (fun y : Rn m ↦ ∫⁻ x in B ∩ f ⁻¹' {y}, φ x ∂μHE[k]) volume ∧ ∫⁻ x in B, φ x * ENNReal.ofReal (coareaJacobian (approxTangentPlane (m + k) M θ x) f x) ∂μHE[m + k] = ∫⁻ y, (∫⁻ x in B ∩ f ⁻¹' {y}, φ x ∂μHE[k]) ∂volume`

## Sibling prerequisites

- `root.coarea_and_slices-a1.c1_parametric_coarea-a1`
- `root.coarea_and_slices-a1.jacobian_identification-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
