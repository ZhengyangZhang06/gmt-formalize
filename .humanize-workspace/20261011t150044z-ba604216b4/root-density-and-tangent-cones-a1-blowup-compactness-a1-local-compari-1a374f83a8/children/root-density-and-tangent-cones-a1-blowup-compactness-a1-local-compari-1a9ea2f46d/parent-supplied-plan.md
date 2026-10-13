# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.lipschitz_leibniz-a1.piece_weak_limit-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-1a9ea2f46d/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.lipschitz_leibniz-a1`
- Child key: `piece_weak_limit`
- Declaration: `Submission.dtc_bc_lc_sl_ll_piece_weak_limit`
- Exact Lean type: `∀ (P n : ℕ) (ψ : Euclid (n + 1) → Euclid P) (V Y : Set (Euclid (n + 1))) (F : Euclid (n + 1) → ℝ) (h : Euclid P → ℝ) (K : NNReal) (G : Euclid P → Euclid P) (hs : ℕ → Euclid P → ℝ) (w : Euclid P → Euclid P), IsOpen V → ContDiff ℝ 1 ψ → InjOn ψ V → (∀ y ∈ V, Injective (fderiv ℝ ψ y)) → ContDiff ℝ 1 F → MeasurableSet Y → IsCompact (closure Y) → closure Y ⊆ V → LipschitzWith K h → (∀ y ∈ Y, h (ψ y) = F y) → (∀ k, ContDiff ℝ 1 (hs k)) → (∀ k x, ‖fderiv ℝ (hs k) x‖ ≤ K) → TendstoUniformly hs h atTop → (∀ᵐ x ∂(μHE[n + 1].restrict (ψ '' Y)), ∀ y ∈ Y, ψ y = x → ∀ e : Euclid (n + 1), inner ℝ (G x) (fderiv ℝ ψ y e) = fderiv ℝ F y e) → IntegrableOn w (ψ '' Y) μHE[n + 1] → (∀ᵐ x ∂(μHE[n + 1].restrict (ψ '' Y)), ∀ y ∈ Y, ψ y = x → w x ∈ LinearMap.range (fderiv ℝ ψ y : Euclid (n + 1) →ₗ[ℝ] Euclid P)) → Tendsto (fun k => ∫ x in ψ '' Y, fderiv ℝ (hs k) x (w x) ∂μHE[n + 1]) atTop (𝓝 (∫ x in ψ '' Y, inner ℝ (G x) (w x) ∂μHE[n + 1]))`

## Sibling prerequisites

- `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.lipschitz_leibniz-a1.grad_weak_limit-a1`
- `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.lipschitz_leibniz-a1.chart_pullback-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
