# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.chart_coarea-a1.slice_disks-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-d5d86bc8d6/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.chart_coarea-a1`
- Child key: `slice_disks`
- Declaration: `Submission.dtc_bc_lc_sl_cc_slice_disks`
- Exact Lean type: `∀ (P n : ℕ) (ψ : Euclid (n + 1) → Euclid P) (V : Set (Euclid (n + 1))) (F : Euclid (n + 1) → ℝ) (t : ℝ), IsOpen V → ContDiff ℝ 1 ψ → InjOn ψ V → (∀ y ∈ V, Injective (fderiv ℝ ψ y)) → ContDiff ℝ 1 F → ∃ (U : ℕ → Set (Euclid n)) (a : ℕ → Euclid n) (r : ℕ → ℝ) (χ : ℕ → Euclid n → Euclid P), (∀ j, IsOpen (U j) ∧ closedBall (a j) (r j) ⊆ U j ∧ ContDiffOn ℝ 1 (χ j) (U j) ∧ InjOn (χ j) (U j) ∧ CountablyRectifiable n (χ j '' U j) ∧ μHE[n] (χ j '' closedBall (a j) (r j)) ≠ ∞ ∧ ∀ w ∈ U j, Injective (fderiv ℝ (χ j) w) ∧ ∃ y ∈ V, ψ y = χ j w ∧ F y = t ∧ fderiv ℝ F y ≠ 0 ∧ ∀ v ∈ LinearMap.range (fderiv ℝ ψ y : Euclid (n + 1) →ₗ[ℝ] Euclid P), (∀ e, inner ℝ v (fderiv ℝ ψ y e) = fderiv ℝ F y e) → LinearMap.range (fderiv ℝ (χ j) w : Euclid n →ₗ[ℝ] Euclid P) = LinearMap.range (fderiv ℝ ψ y : Euclid (n + 1) →ₗ[ℝ] Euclid P) ⊓ (ℝ ∙ v)ᗮ) ∧ ψ '' {y | y ∈ V ∧ F y = t ∧ fderiv ℝ F y ≠ 0} ⊆ ⋃ j, χ j '' ball (a j) (r j)`

## Sibling prerequisites

- `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.chart_coarea-a1.flattening_atlas-a1`
- `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.chart_coarea-a1.slice_param-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
