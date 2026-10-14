# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.zero_scale_limit_plane-a1.flat_limit-a1.perimeter_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-zer-c6ed2a06b3/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.zero_scale_limit_plane-a1.flat_limit-a1`
- Child key: `perimeter_bound`
- Declaration: `Submission.codim1_zsl_fl_perimeter_bound`
- Exact Lean type: `∀ (n k : ℕ) (Us : ℕ → Set (Euclid (n + 1 + k))) (Ss : (i : ℕ) → GeometricCurrentOn (Us i) n) (ι : Euclid (n + 1) →ₗᵢ[ℝ] Euclid (n + 1 + k)) (ι' : Euclid k →ₗᵢ[ℝ] Euclid (n + 1 + k)) (b : Euclid k) (gs : ℕ → Euclid (n + 1) → Euclid k) (Fs : ℕ → Set (Euclid (n + 1))), (∀ v w, inner ℝ (ι v) (ι' w) = 0) → (∀ y : Euclid (n + 1 + k), ∃ v w, y = ι v + ι' w) → (∀ i, MeasurableSet (Fs i)) → (∀ R : ℝ, 0 < R → ∀ᶠ i in atTop, ∀ w ∈ ball (0 : Euclid (n + 1)) R, DifferentiableAt ℝ (gs i) w) → (∀ R ε : ℝ, 0 < R → 0 < ε → ∀ᶠ i in atTop, ∀ w ∈ ball (0 : Euclid (n + 1)) R, ‖gs i w - b‖ < ε ∧ ‖fderiv ℝ (gs i) w‖ < ε) → (∀ R : ℝ, 0 < R → ∀ᶠ i in atTop, ∀ ω : TestFormOn (univ : Set (Euclid (n + 1 + k))) n, tsupport (ω : DifferentialForm (Euclid (n + 1 + k)) n) ⊆ ball 0 R → currentEval (Ss i) (ω : DifferentialForm (Euclid (n + 1 + k)) n) = ∫ w in Fs i ∩ ball 0 R, exteriorDerivative (ω : DifferentialForm (Euclid (n + 1 + k)) n) (ι w + ι' (gs i w)) (fun j => fderiv ℝ (fun w => ι w + ι' (gs i w)) w (EuclideanSpace.single j (1 : ℝ)))) → (∀ R : ℝ, 0 < R → ∃ c : ℝ, ∀ᶠ i in atTop, ∀ ω : TestFormOn (univ : Set (Euclid (n + 1 + k))) n, tsupport (ω : DifferentialForm (Euclid (n + 1 + k)) n) ⊆ ball 0 R → (∀ y, covectorEuclideanNorm ((ω : DifferentialForm (Euclid (n + 1 + k)) n) y) ≤ 1) → currentEval (Ss i) (ω : DifferentialForm (Euclid (n + 1 + k)) n) ≤ c) → ∀ R : ℝ, 0 < R → ∃ c : ℝ, ∀ᶠ i in atTop, ∀ φ : Euclid (n + 1) → Euclid (n + 1), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ ball 0 R → (∀ v, ‖φ v‖ ≤ 1) → ∫ v in Fs i, LinearMap.trace ℝ (Euclid (n + 1)) (fderiv ℝ φ v).toLinearMap ≤ c`

## Sibling prerequisites

- `root.dimension_reduction_results-a1.codimension_one_regularity-a1.zero_scale_limit_plane-a1.flat_limit-a1.divergence_lift-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
