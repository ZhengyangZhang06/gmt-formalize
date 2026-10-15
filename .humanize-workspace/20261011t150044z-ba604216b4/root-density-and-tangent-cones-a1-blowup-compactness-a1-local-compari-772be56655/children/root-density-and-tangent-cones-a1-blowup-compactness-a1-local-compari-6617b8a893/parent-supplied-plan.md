# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.coarea-a1.chart_bilipschitz-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-6617b8a893/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.coarea-a1`
- Child key: `chart_bilipschitz`
- Declaration: `Submission.dtc_bc_lc_sl_co_chart_bilipschitz`
- Exact Lean type: `∀ (P d : ℕ) (ψ : Euclid d → Euclid P) (K : Set (Euclid d)), ContDiff ℝ 1 ψ → IsCompact K → InjOn ψ K → (∀ y ∈ K, Injective (fderiv ℝ ψ y)) → ∃ m Λ : ℝ, 0 < m ∧ ∀ a ∈ K, ∀ b ∈ K, m * ‖a - b‖ ≤ ‖ψ a - ψ b‖ ∧ ‖ψ a - ψ b‖ ≤ Λ * ‖a - b‖`

## Sibling prerequisites

- `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.rectifiable_density_one-a1.c1_cover-a1.local_lower_lipschitz-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
