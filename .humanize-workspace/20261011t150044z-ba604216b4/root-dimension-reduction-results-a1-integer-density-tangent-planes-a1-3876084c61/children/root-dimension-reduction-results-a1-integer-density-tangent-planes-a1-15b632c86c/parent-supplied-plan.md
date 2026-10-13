# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_constant_density_planar-a1.stationary_cone_sheet_planar-a1.cone_conservation-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-15b632c86c/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_constant_density_planar-a1.stationary_cone_sheet_planar-a1`
- Child key: `cone_conservation`
- Declaration: `Submission.idtp_ccd_scsp_cone_conservation`
- Exact Lean type: `∀ (P : ℕ) (u e : Euclid P) (r₀ s : ℝ) (N : Set (Euclid P)) (γ : ℝ → Euclid P) (T : Euclid P → Submodule ℝ (Euclid P)), ‖u‖ = 1 → ‖e‖ = 1 → inner ℝ u e = 0 → 0 < s → s < r₀ → IsOpen N → (∀ x ∈ N, 0 < inner ℝ x u) → ContDiffOn ℝ 1 γ (Ioo (-s) s) → (∀ α ∈ Ioo (-s) s, ‖γ α‖ = 1 ∧ 0 < inner ℝ (γ α) u ∧ Real.arctan (inner ℝ (γ α) e / inner ℝ (γ α) u) = α) → (∀ t ∈ Ioo (r₀ - s) (r₀ + s), ∀ α ∈ Ioo (-s) s, t • γ α ∈ N ∧ T (t • γ α) = Submodule.span ℝ {γ α, deriv γ α}) → (∀ X : Euclid P → Euclid P, ContDiff ℝ 1 X → HasCompactSupport X → tsupport X ⊆ N → ∫ x in (fun q : ℝ × ℝ => q.1 • γ q.2) '' (Ioo (r₀ - s) (r₀ + s) ×ˢ Ioo (-s) s), LinearMap.trace ℝ (Euclid P) ((T x).starProjection.toLinearMap ∘ₗ (fderiv ℝ X x).toLinearMap) ∂μHE[2] = 0) → ∀ φ : ℝ → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ Ioo (-s) s → ∫ α, deriv φ α * ((inner ℝ (γ α) u ^ 2 + inner ℝ (γ α) e ^ 2) / ‖deriv γ α‖) = 0`

## Sibling prerequisites

- `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_constant_density_planar-a1.stationary_cone_sheet_planar-a1.angle_curve-a1`
- `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_constant_density_planar-a1.stationary_cone_sheet_planar-a1.cone_area-a1`
- `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_constant_density_planar-a1.stationary_cone_sheet_planar-a1.test_field-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
