# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.coarea-a1.approx_differentiable-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-41c94d66e6/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.coarea-a1`
- Child key: `approx_differentiable`
- Declaration: `Submission.dtc_bc_lc_sl_co_approx_differentiable`
- Exact Lean type: `∀ (P d : ℕ) (M : Set (Euclid P)) (f : Euclid P → ℝ) (G : Euclid P → Euclid P) (ψ : ℕ → Euclid d → Euclid P) (V Y : ℕ → Set (Euclid d)) (F : ℕ → Euclid d → ℝ), MeasurableSet M → (∀ K : Set (Euclid P), IsCompact K → μHE[d] (M ∩ K) ≠ ∞) → (∀ j, ContDiff ℝ 1 (ψ j)) → (∀ j, InjOn (ψ j) (V j)) → (∀ j, ∀ y ∈ V j, Injective (fderiv ℝ (ψ j) y)) → (∀ j, ContDiff ℝ 1 (F j)) → (∀ j, IsCompact (closure (Y j))) → (∀ j, closure (Y j) ⊆ V j) → (∀ j, MeasurableSet (ψ j '' Y j)) → (∀ j, ψ j '' Y j ⊆ M) → (∀ j, ∀ y ∈ Y j, f (ψ j y) = F j y) → (∀ j, ∀ y ∈ Y j, HasApproximateTangentSpaceAt d M (ψ j y) (LinearMap.range (fderiv ℝ (ψ j) y : Euclid d →ₗ[ℝ] Euclid P))) → (∀ j, ∀ y ∈ Y j, G (ψ j y) ∈ LinearMap.range (fderiv ℝ (ψ j) y : Euclid d →ₗ[ℝ] Euclid P) ∧ ∀ e : Euclid d, inner ℝ (G (ψ j y)) (fderiv ℝ (ψ j) y e) = fderiv ℝ (F j) y e) → μHE[d] (M \ ⋃ j, ψ j '' Y j) = 0 → ∀ᵐ x ∂(μHE[d].restrict M), HasApproximateTangentSpaceAt d M x (approxTangentPlane d M x) ∧ G x ∈ approxTangentPlane d M x ∧ ∀ ε : ℝ, 0 < ε → Tendsto (fun r : ℝ => μHE[d] (M ∩ ball x r ∩ {y | ε * ‖y - x‖ < |f y - f x - inner ℝ (G x) (y - x)|}) / ENNReal.ofReal (r ^ d)) (𝓝[>] 0) (𝓝 0)`

## Sibling prerequisites

- `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.coarea-a1.chart_bilipschitz-a1`
- `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.coarea-a1.tangent_complement_density-a1`
- `root.compactness_of_minimizing_currents-a1.im_calculus-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
