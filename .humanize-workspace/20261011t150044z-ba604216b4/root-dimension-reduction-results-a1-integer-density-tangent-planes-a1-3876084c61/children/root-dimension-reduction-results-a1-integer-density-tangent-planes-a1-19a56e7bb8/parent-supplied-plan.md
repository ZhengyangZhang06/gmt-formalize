# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_constant_density_planar-a1.stationary_cone_sheet_planar-a1.test_field-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-19a56e7bb8/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_constant_density_planar-a1.stationary_cone_sheet_planar-a1`
- Child key: `test_field`
- Declaration: `Submission.idtp_ccd_scsp_test_field`
- Exact Lean type: `∀ (P : ℕ) (u e : Euclid P) (r₀ s : ℝ) (N : Set (Euclid P)) (γ : ℝ → Euclid P) (T : Euclid P → Submodule ℝ (Euclid P)) (lam φ : ℝ → ℝ), ‖u‖ = 1 → ‖e‖ = 1 → inner ℝ u e = 0 → 0 < s → s < r₀ → IsOpen N → (∀ x ∈ N, 0 < inner ℝ x u) → ContDiffOn ℝ 1 γ (Ioo (-s) s) → (∀ α ∈ Ioo (-s) s, ‖γ α‖ = 1 ∧ 0 < inner ℝ (γ α) u ∧ Real.arctan (inner ℝ (γ α) e / inner ℝ (γ α) u) = α) → (∀ t ∈ Ioo (r₀ - s) (r₀ + s), ∀ α ∈ Ioo (-s) s, t • γ α ∈ N ∧ T (t • γ α) = Submodule.span ℝ {γ α, deriv γ α}) → ContDiff ℝ 1 lam → HasCompactSupport lam → tsupport lam ⊆ Ioo (r₀ - s) (r₀ + s) → ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ Ioo (-s) s → ∃ X : Euclid P → Euclid P, ContDiff ℝ 1 X ∧ HasCompactSupport X ∧ tsupport X ⊆ N ∧ ∀ t ∈ Ioo (r₀ - s) (r₀ + s), ∀ α ∈ Ioo (-s) s, LinearMap.trace ℝ (Euclid P) ((T (t • γ α)).starProjection.toLinearMap ∘ₗ (fderiv ℝ X (t • γ α)).toLinearMap) = lam t * deriv φ α * ((inner ℝ (γ α) u ^ 2 + inner ℝ (γ α) e ^ 2) / ‖deriv γ α‖ ^ 2)`

## Sibling prerequisites

- `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_constant_density_planar-a1.stationary_cone_sheet_planar-a1.angle_curve-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
