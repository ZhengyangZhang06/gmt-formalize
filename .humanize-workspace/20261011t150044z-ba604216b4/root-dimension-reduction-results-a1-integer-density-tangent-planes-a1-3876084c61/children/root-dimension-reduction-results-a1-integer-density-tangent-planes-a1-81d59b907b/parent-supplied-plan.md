# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_constant_density_planar-a1.stationary_cone_sheet_planar-a1.cone_area-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-81d59b907b/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_constant_density_planar-a1.stationary_cone_sheet_planar-a1`
- Child key: `cone_area`
- Declaration: `Submission.idtp_ccd_scsp_cone_area`
- Exact Lean type: `∀ (P : ℕ) (r₀ s : ℝ) (γ : ℝ → Euclid P) (h : Euclid P → ℝ), 0 < s → s < r₀ → ContDiffOn ℝ 1 γ (Ioo (-s) s) → InjOn γ (Ioo (-s) s) → (∀ α ∈ Ioo (-s) s, ‖γ α‖ = 1 ∧ inner ℝ (γ α) (deriv γ α) = 0 ∧ deriv γ α ≠ 0) → ∫ x in (fun q : ℝ × ℝ => q.1 • γ q.2) '' (Ioo (r₀ - s) (r₀ + s) ×ˢ Ioo (-s) s), h x ∂μHE[2] = ∫ q in Ioo (r₀ - s) (r₀ + s) ×ˢ Ioo (-s) s, q.1 * ‖deriv γ q.2‖ * h (q.1 • γ q.2)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
