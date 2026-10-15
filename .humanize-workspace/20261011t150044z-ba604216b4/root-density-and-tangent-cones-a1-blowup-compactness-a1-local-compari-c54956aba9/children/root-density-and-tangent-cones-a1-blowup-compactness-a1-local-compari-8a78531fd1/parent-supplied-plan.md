# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.chart_pieces-a1.chart_tangent-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-8a78531fd1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.chart_pieces-a1`
- Child key: `chart_tangent`
- Declaration: `Submission.dtc_bc_lc_sl_cp_chart_tangent`
- Exact Lean type: `∀ (P N : ℕ) (M : Set (Euclid P)) (g : Euclid N → Euclid P) (c : Euclid N) (r m : ℝ), MeasurableSet M → (∀ K : Set (Euclid P), IsCompact K → μHE[N] (M ∩ K) ≠ ∞) → ContDiff ℝ 1 g → 0 < m → (∀ a ∈ ball c r, ∀ b ∈ ball c r, m * ‖a - b‖ ≤ ‖g a - g b‖) → MeasurableSet (g '' ball c r) → μHE[N] (g '' ball c r) ≠ ∞ → ∃ E : Set (Euclid P), MeasurableSet E ∧ μHE[N] E = 0 ∧ ∀ y ∈ ball c r, g y ∈ M → g y ∉ E → HasApproximateTangentSpaceAt N M (g y) (LinearMap.range (fderiv ℝ g y : Euclid N →ₗ[ℝ] Euclid P))`

## Sibling prerequisites

- `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.rectifiable_density_one-a1.c1_piece_tangent-a1`
- `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.graph_tangent-a1.tangent_transfer-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
