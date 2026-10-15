# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.chart_coarea-a1.chart_gradient-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-ec042f9d52/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.chart_coarea-a1`
- Child key: `chart_gradient`
- Declaration: `Submission.dtc_bc_lc_sl_cc_chart_gradient`
- Exact Lean type: `∀ (P N : ℕ) (ψ : Euclid N → Euclid P) (V : Set (Euclid N)) (F : Euclid N → ℝ), IsOpen V → ContDiff ℝ 1 ψ → (∀ y ∈ V, Injective (fderiv ℝ ψ y)) → ContDiff ℝ 1 F → ∃ Gh : Euclid N → Euclid P, Measurable Gh ∧ ContinuousOn Gh V ∧ ∀ y ∈ V, Gh y ∈ LinearMap.range (fderiv ℝ ψ y : Euclid N →ₗ[ℝ] Euclid P) ∧ (∀ e, inner ℝ (Gh y) (fderiv ℝ ψ y e) = fderiv ℝ F y e) ∧ (∀ v ∈ LinearMap.range (fderiv ℝ ψ y : Euclid N →ₗ[ℝ] Euclid P), (∀ e, inner ℝ v (fderiv ℝ ψ y e) = fderiv ℝ F y e) → v = Gh y) ∧ (Gh y = 0 ↔ fderiv ℝ F y = 0)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
