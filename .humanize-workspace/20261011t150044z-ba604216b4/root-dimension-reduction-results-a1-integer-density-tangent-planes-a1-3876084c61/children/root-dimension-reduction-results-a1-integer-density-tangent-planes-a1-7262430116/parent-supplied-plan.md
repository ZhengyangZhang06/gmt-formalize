# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_constant_density_planar-a1.stationary_cone_sheet_planar-a1.cone_chart-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-7262430116/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_constant_density_planar-a1.stationary_cone_sheet_planar-a1`
- Child key: `cone_chart`
- Declaration: `Submission.idtp_ccd_scsp_cone_chart`
- Exact Lean type: `∀ (P : ℕ) (M : Set (Euclid P)) (u : Euclid P) (r₀ ρ : ℝ), IsEmbeddedSubmanifold 1 2 M → ‖u‖ = 1 → 0 < r₀ → r₀ • u ∈ M → 0 < ρ → (∀ x ∈ M ∩ ball (r₀ • u) ρ, ∀ t : ℝ, 0 < t → t • x ∈ ball (r₀ • u) ρ → t • x ∈ M) → ∃ (e : Euclid P) (s : ℝ) (N : Set (Euclid P)) (γ : ℝ → Euclid P), ‖e‖ = 1 ∧ inner ℝ u e = 0 ∧ 0 < s ∧ s < r₀ ∧ IsOpen N ∧ r₀ • u ∈ N ∧ N ⊆ ball (r₀ • u) ρ ∧ (∀ x ∈ N, 0 < inner ℝ x u) ∧ ContDiffOn ℝ 1 γ (Ioo (-s) s) ∧ γ 0 = u ∧ deriv γ 0 = e ∧ (∀ α ∈ Ioo (-s) s, ‖γ α‖ = 1 ∧ 0 < inner ℝ (γ α) u ∧ Real.arctan (inner ℝ (γ α) e / inner ℝ (γ α) u) = α) ∧ M ∩ N = (fun q : ℝ × ℝ => q.1 • γ q.2) '' (Ioo (r₀ - s) (r₀ + s) ×ˢ Ioo (-s) s) ∧ ∀ t ∈ Ioo (r₀ - s) (r₀ + s), ∀ α ∈ Ioo (-s) s, Submodule.span ℝ (tangentSpace M (t • γ α)) = Submodule.span ℝ {γ α, deriv γ α}`

## Sibling prerequisites

- `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_constant_density_planar-a1.stationary_cone_sheet_planar-a1.tangent_plane_mem-a1`
- `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_constant_density_planar-a1.stationary_cone_sheet_planar-a1.local_inverse-a1`
- `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_constant_density_planar-a1.stationary_cone_sheet_planar-a1.angle_curve-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
