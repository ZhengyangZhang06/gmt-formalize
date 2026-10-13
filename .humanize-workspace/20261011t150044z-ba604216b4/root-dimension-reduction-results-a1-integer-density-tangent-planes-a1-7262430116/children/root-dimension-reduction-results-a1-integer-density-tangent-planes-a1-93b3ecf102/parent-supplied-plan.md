# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_constant_density_planar-a1.stationary_cone_sheet_planar-a1.cone_chart-a1.radial_extension-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-93b3ecf102/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_constant_density_planar-a1.stationary_cone_sheet_planar-a1.cone_chart-a1`
- Child key: `radial_extension`
- Declaration: `Submission.idtp_ccd_scsp_cc_radial_extension`
- Exact Lean type: `∀ (P : ℕ) (M N : Set (Euclid P)) (p : Euclid P) (ρ r₀ s : ℝ) (F : Euclid P → Euclid 2) (G : Euclid 2 → Euclid P) (γ : ℝ → Euclid P), 0 < s → s < r₀ → IsOpen N → N ⊆ ball p ρ → (∀ x ∈ M ∩ ball p ρ, ∀ t : ℝ, 0 < t → t • x ∈ ball p ρ → t • x ∈ M) → ContinuousOn G {w : Euclid 2 | w 0 ∈ Ioo (r₀ - s) (r₀ + s) ∧ w 1 ∈ Ioo (-s) s} → M ∩ N = G '' {w : Euclid 2 | w 0 ∈ Ioo (r₀ - s) (r₀ + s) ∧ w 1 ∈ Ioo (-s) s} → (∀ w : Euclid 2, w 0 ∈ Ioo (r₀ - s) (r₀ + s) → w 1 ∈ Ioo (-s) s → F (G w) = w) → (∀ α ∈ Ioo (-s) s, ‖γ α‖ = 1 ∧ G !₂[r₀, α] = r₀ • γ α ∧ ∀ t : ℝ, 0 < t → F (t • γ α) = !₂[t, α]) → (∀ w : Euclid 2, w 0 ∈ Ioo (r₀ - s) (r₀ + s) → w 1 ∈ Ioo (-s) s → G w = w 0 • γ (w 1)) ∧ M ∩ N = (fun q : ℝ × ℝ => q.1 • γ q.2) '' (Ioo (r₀ - s) (r₀ + s) ×ˢ Ioo (-s) s)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
