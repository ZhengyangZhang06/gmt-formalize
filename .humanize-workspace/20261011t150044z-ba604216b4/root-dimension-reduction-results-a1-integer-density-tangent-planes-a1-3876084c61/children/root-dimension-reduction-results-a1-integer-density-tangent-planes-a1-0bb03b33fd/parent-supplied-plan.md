# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_constant_density_planar-a1.stationary_cone_sheet_planar-a1.sector_plane-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-0bb03b33fd/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_constant_density_planar-a1.stationary_cone_sheet_planar-a1`
- Child key: `sector_plane`
- Declaration: `Submission.idtp_ccd_scsp_sector_plane`
- Exact Lean type: `∀ (P : ℕ) (M N : Set (Euclid P)) (u e : Euclid P) (r₀ s : ℝ), ‖u‖ = 1 → ‖e‖ = 1 → inner ℝ u e = 0 → 0 < s → s < r₀ → IsOpen N → r₀ • u ∈ N → M ∩ N = (fun q : ℝ × ℝ => q.1 • (Real.cos q.2 • u + Real.sin q.2 • e)) '' (Ioo (r₀ - s) (r₀ + s) ×ˢ Ioo (-s) s) → ∃ δ : ℝ, 0 < δ ∧ M ∩ ball (r₀ • u) δ = (Submodule.span ℝ {u, e} : Set (Euclid P)) ∩ ball (r₀ • u) δ`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
