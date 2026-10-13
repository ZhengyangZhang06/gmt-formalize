# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.chart_pieces-a1.chart_refinement-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-0ffc0e068a/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.chart_pieces-a1`
- Child key: `chart_refinement`
- Declaration: `Submission.dtc_bc_lc_sl_cp_chart_refinement`
- Exact Lean type: `∀ (P N : ℕ) (M : Set (Euclid P)) (f : Euclid P → ℝ) (L : NNReal) (ψ : Euclid N → Euclid P) (V : Set (Euclid N)), MeasurableSet M → LipschitzWith L f → IsOpen V → ContDiff ℝ 1 ψ → ∃ (Y : ℕ → Set (Euclid N)) (F : ℕ → Euclid N → ℝ), (∀ k, ContDiff ℝ 1 (F k) ∧ MeasurableSet (Y k) ∧ IsCompact (closure (Y k)) ∧ closure (Y k) ⊆ V ∧ ψ '' Y k ⊆ M ∧ ∀ y ∈ Y k, f (ψ y) = F k y) ∧ μHE[N] ((M ∩ ψ '' V) \ ⋃ k, ψ '' Y k) = 0`

## Sibling prerequisites

- `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.rectifiable_density_one-a1.c1_approximation-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
