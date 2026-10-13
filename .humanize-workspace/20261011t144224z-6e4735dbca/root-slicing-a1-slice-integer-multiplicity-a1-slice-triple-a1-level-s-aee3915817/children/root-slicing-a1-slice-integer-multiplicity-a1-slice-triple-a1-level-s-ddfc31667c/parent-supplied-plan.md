# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.slicing-a1.slice_integer_multiplicity-a1.slice_triple-a1.level_set_charts-a1.tangent_range-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1-slice-triple-a1-level-s-ddfc31667c/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.slicing-a1.slice_integer_multiplicity-a1.slice_triple-a1.level_set_charts-a1`
- Child key: `tangent_range`
- Declaration: `Submission.slicing_im_st_lsc_tangent_range`
- Exact Lean type: `∀ (P m : ℕ) (ψ : Eucl m → Eucl (m + 1)) (Φ : Eucl (m + 1) → Eucl P) (h : Eucl (m + 1) → ℝ) (V : Set (Eucl m)) (c : ℝ) (v : Eucl m), IsOpen V → v ∈ V → 0 < c → DifferentiableAt ℝ ψ v → DifferentiableAt ℝ Φ (ψ v) → DifferentiableAt ℝ h (ψ v) → fderiv ℝ h (ψ v) ≠ 0 → (∀ v' ∈ V, ∀ v'' ∈ V, c * ‖v' - v''‖ ≤ ‖ψ v' - ψ v''‖) → (∀ v' ∈ V, h (ψ v') = h (ψ v)) → LinearMap.range (fderiv ℝ (Φ ∘ ψ) v).toLinearMap = Submodule.map (fderiv ℝ Φ (ψ v)).toLinearMap (LinearMap.ker (fderiv ℝ h (ψ v)).toLinearMap)`

## Sibling prerequisites

- `root.lipschitz_pushforward_im-a1.weighted_tangent_on_c1_chart-a1.chart_approximate_tangent-a1.fderiv_lower_bound-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
