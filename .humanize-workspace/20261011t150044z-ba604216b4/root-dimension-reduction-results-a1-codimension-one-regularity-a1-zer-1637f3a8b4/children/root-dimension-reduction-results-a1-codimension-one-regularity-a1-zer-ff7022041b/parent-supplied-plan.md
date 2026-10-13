# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.zero_scale_limit_plane-a1.flat_limit-a1.divergence_lift-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-zer-ff7022041b/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.zero_scale_limit_plane-a1.flat_limit-a1`
- Child key: `divergence_lift`
- Declaration: `Submission.codim1_zsl_fl_divergence_lift`
- Exact Lean type: `∀ (n k : ℕ) (ι : Euclid (n + 1) →ₗᵢ[ℝ] Euclid (n + 1 + k)) (ι' : Euclid k →ₗᵢ[ℝ] Euclid (n + 1 + k)), (∀ v w, inner ℝ (ι v) (ι' w) = 0) → (∀ y : Euclid (n + 1 + k), ∃ v w, y = ι v + ι' w) → ∃ K : ℝ, 0 < K ∧ ∀ h R : ℝ, 0 < h → ∀ φ : Euclid (n + 1) → Euclid (n + 1), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ ball 0 R → (∀ v, ‖φ v‖ ≤ 1) → ∃ ω : TestFormOn (univ : Set (Euclid (n + 1 + k))) n, tsupport (ω : DifferentialForm (Euclid (n + 1 + k)) n) ⊆ ball 0 (R + 2 * h) ∧ (∀ y, covectorEuclideanNorm ((ω : DifferentialForm (Euclid (n + 1 + k)) n) y) ≤ 1) ∧ ∀ (g : Euclid (n + 1) → Euclid k) (v : Euclid (n + 1)), DifferentiableAt ℝ g v → ‖g v‖ < h → exteriorDerivative (ω : DifferentialForm (Euclid (n + 1 + k)) n) (ι v + ι' (g v)) (fun j => fderiv ℝ (fun w => ι w + ι' (g w)) v (EuclideanSpace.single j (1 : ℝ))) = K⁻¹ * LinearMap.trace ℝ (Euclid (n + 1)) (fderiv ℝ φ v).toLinearMap`

## Sibling prerequisites

- `root.density_one_implies_regular-a1.epsilon_regularity-a1.graph_cycle_regular-a1.boundary_weak_derivatives-a1.coordinate_covector-a1`
- `root.density_one_implies_regular-a1.epsilon_regularity-a1.graph_cycle_regular-a1.boundary_weak_derivatives-a1.graph_pullback_extderiv-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
