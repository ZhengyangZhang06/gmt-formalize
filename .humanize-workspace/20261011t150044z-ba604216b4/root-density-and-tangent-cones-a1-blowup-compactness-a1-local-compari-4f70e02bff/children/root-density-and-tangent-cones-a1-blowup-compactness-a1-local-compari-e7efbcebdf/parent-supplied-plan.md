# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.chart_coarea-a1.flattening_atlas-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-e7efbcebdf/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.chart_coarea-a1`
- Child key: `flattening_atlas`
- Declaration: `Submission.dtc_bc_lc_sl_cc_flattening_atlas`
- Exact Lean type: `∀ (n : ℕ) (F : Euclid (n + 1) → ℝ) (V : Set (Euclid (n + 1))), IsOpen V → ContDiff ℝ 1 F → ∃ (Ω : ℕ → Set (Euclid (n + 1))) (Θ : ℕ → Euclid (n + 1) → Euclid (n + 1)), (∀ k, IsOpen (Ω k) ∧ ContDiffOn ℝ 1 (Θ k) (Ω k) ∧ InjOn (Θ k) (Ω k) ∧ (∀ z ∈ Ω k, Injective (fderiv ℝ (Θ k) z)) ∧ IsOpen (Θ k '' Ω k) ∧ Θ k '' Ω k ⊆ V ∧ ∀ z ∈ Ω k, F (Θ k z) = z 0) ∧ {y | y ∈ V ∧ fderiv ℝ F y ≠ 0} ⊆ ⋃ k, Θ k '' Ω k`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
