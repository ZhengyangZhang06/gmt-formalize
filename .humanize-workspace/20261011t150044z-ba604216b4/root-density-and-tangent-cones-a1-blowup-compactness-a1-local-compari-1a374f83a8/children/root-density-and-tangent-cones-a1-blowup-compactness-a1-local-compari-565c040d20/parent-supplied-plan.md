# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.lipschitz_leibniz-a1.piece_gradient-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-565c040d20/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.lipschitz_leibniz-a1`
- Child key: `piece_gradient`
- Declaration: `Submission.dtc_bc_lc_sl_ll_piece_gradient`
- Exact Lean type: `∀ (P n : ℕ) (M : Set (Euclid P)) (ψ : Euclid (n + 1) → Euclid P) (V Y : Set (Euclid (n + 1))) (F : Euclid (n + 1) → ℝ) (h : Euclid P → ℝ) (H : Euclid P → Euclid P), MeasurableSet M → (∀ C : Set (Euclid P), IsCompact C → μHE[n + 1] (M ∩ C) ≠ ∞) → IsOpen V → ContDiff ℝ 1 ψ → InjOn ψ V → (∀ y ∈ V, Injective (fderiv ℝ ψ y)) → ContDiff ℝ 1 F → MeasurableSet Y → IsCompact (closure Y) → closure Y ⊆ V → ψ '' Y ⊆ M → (∀ y ∈ Y, h (ψ y) = F y) → (∀ y ∈ Y, HasApproximateTangentSpaceAt (n + 1) M (ψ y) (LinearMap.range (fderiv ℝ ψ y : Euclid (n + 1) →ₗ[ℝ] Euclid P))) → (∀ᵐ x ∂(μHE[n + 1].restrict M), HasApproximateTangentSpaceAt (n + 1) M x (approxTangentPlane (n + 1) M x) ∧ H x ∈ approxTangentPlane (n + 1) M x ∧ ∀ ε : ℝ, 0 < ε → Tendsto (fun r : ℝ => μHE[n + 1] (M ∩ ball x r ∩ {y | ε * ‖y - x‖ < |h y - h x - inner ℝ (H x) (y - x)|}) / ENNReal.ofReal (r ^ (n + 1))) (𝓝[>] 0) (𝓝 0)) → ∀ᵐ x ∂(μHE[n + 1].restrict (ψ '' Y)), ∀ y ∈ Y, ψ y = x → H x ∈ LinearMap.range (fderiv ℝ ψ y : Euclid (n + 1) →ₗ[ℝ] Euclid P) ∧ ∀ e : Euclid (n + 1), inner ℝ (H x) (fderiv ℝ ψ y e) = fderiv ℝ F y e`

## Sibling prerequisites

- `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.lipschitz_leibniz-a1.approx_grad_unique-a1`
- `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.lipschitz_leibniz-a1.immersion_antilipschitz-a1`
- `root.compactness_of_minimizing_currents-a1.im_calculus-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
