# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.coarea-a1.chart_gradient-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-87919f64c2/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.coarea-a1`
- Child key: `chart_gradient`
- Declaration: `Submission.dtc_bc_lc_sl_co_chart_gradient`
- Exact Lean type: `∀ (P d : ℕ) (ψ : Euclid d → Euclid P) (F : Euclid d → ℝ) (V : Set (Euclid d)), ContDiff ℝ 1 ψ → ContDiff ℝ 1 F → (∀ y ∈ V, Injective (fderiv ℝ ψ y)) → ∃ h : Euclid d → Euclid P, ContinuousOn h V ∧ ∀ y ∈ V, h y ∈ LinearMap.range (fderiv ℝ ψ y : Euclid d →ₗ[ℝ] Euclid P) ∧ ∀ e : Euclid d, inner ℝ (h y) (fderiv ℝ ψ y e) = fderiv ℝ F y e`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
