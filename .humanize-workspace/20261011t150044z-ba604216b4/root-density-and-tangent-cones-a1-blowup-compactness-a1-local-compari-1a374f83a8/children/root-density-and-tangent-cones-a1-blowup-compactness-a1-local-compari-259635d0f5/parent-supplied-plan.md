# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.lipschitz_leibniz-a1.chart_pullback-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-259635d0f5/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.lipschitz_leibniz-a1`
- Child key: `chart_pullback`
- Declaration: `Submission.dtc_bc_lc_sl_ll_chart_pullback`
- Exact Lean type: `∀ (P n : ℕ) (ψ : Euclid (n + 1) → Euclid P) (V Y : Set (Euclid (n + 1))), IsOpen V → ContDiff ℝ 1 ψ → InjOn ψ V → (∀ y ∈ V, Injective (fderiv ℝ ψ y)) → MeasurableSet Y → IsCompact (closure Y) → closure Y ⊆ V → (∀ p : Euclid P → Prop, (∀ᵐ x ∂(μHE[n + 1].restrict (ψ '' Y)), p x) → ∀ᵐ y ∂(volume.restrict Y), p (ψ y)) ∧ ∀ w : Euclid P → Euclid P, IntegrableOn w (ψ '' Y) μHE[n + 1] → (∀ᵐ x ∂(μHE[n + 1].restrict (ψ '' Y)), ∀ y ∈ Y, ψ y = x → w x ∈ LinearMap.range (fderiv ℝ ψ y : Euclid (n + 1) →ₗ[ℝ] Euclid P)) → ∃ W : Euclid (n + 1) → Euclid (n + 1), Integrable W ∧ (∀ y, y ∉ Y → W y = 0) ∧ ∀ ℓ : Euclid P → (Euclid P →L[ℝ] ℝ), ∫ x in ψ '' Y, ℓ x (w x) ∂μHE[n + 1] = ∫ y, ℓ (ψ y) (fderiv ℝ ψ y (W y))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
