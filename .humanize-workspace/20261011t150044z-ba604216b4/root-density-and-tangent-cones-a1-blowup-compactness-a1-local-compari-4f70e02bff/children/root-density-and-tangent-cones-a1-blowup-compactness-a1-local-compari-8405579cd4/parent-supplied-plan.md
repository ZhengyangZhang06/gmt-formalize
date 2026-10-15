# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.chart_coarea-a1.slice_param-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-8405579cd4/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.chart_coarea-a1`
- Child key: `slice_param`
- Declaration: `Submission.dtc_bc_lc_sl_cc_slice_param`
- Exact Lean type: `∀ (P n : ℕ) (c : ℝ → Euclid n → Euclid (n + 1)) (ψ : Euclid (n + 1) → Euclid P) (V Ω : Set (Euclid (n + 1))) (F : Euclid (n + 1) → ℝ) (Θ : Euclid (n + 1) → Euclid (n + 1)) (t : ℝ), (∀ s w, c s w 0 = s ∧ ∀ i : Fin n, c s w i.succ = w i) → ContDiff ℝ 1 ψ → InjOn ψ V → (∀ y ∈ V, Injective (fderiv ℝ ψ y)) → ContDiff ℝ 1 F → IsOpen Ω → ContDiffOn ℝ 1 Θ Ω → InjOn Θ Ω → (∀ z ∈ Ω, Injective (fderiv ℝ Θ z)) → Θ '' Ω ⊆ V → (∀ z ∈ Ω, F (Θ z) = z 0) → IsOpen {w | c t w ∈ Ω} ∧ ContDiffOn ℝ 1 (fun w => ψ (Θ (c t w))) {w | c t w ∈ Ω} ∧ InjOn (fun w => ψ (Θ (c t w))) {w | c t w ∈ Ω} ∧ ∀ w, c t w ∈ Ω → fderiv ℝ F (Θ (c t w)) ≠ 0 ∧ Injective (fderiv ℝ (fun w' => ψ (Θ (c t w'))) w) ∧ ∀ v ∈ LinearMap.range (fderiv ℝ ψ (Θ (c t w)) : Euclid (n + 1) →ₗ[ℝ] Euclid P), (∀ e, inner ℝ v (fderiv ℝ ψ (Θ (c t w)) e) = fderiv ℝ F (Θ (c t w)) e) → LinearMap.range (fderiv ℝ (fun w' => ψ (Θ (c t w'))) w : Euclid n →ₗ[ℝ] Euclid P) = LinearMap.range (fderiv ℝ ψ (Θ (c t w)) : Euclid (n + 1) →ₗ[ℝ] Euclid P) ⊓ (ℝ ∙ v)ᗮ ∧ Real.sqrt (((fderiv ℝ (fun w' => ψ (Θ (c t w'))) w).adjoint ∘L fderiv ℝ (fun w' => ψ (Θ (c t w'))) w).det) = ‖v‖ * Real.sqrt (((fderiv ℝ ψ (Θ (c t w))).adjoint ∘L fderiv ℝ ψ (Θ (c t w))).det) * |(fderiv ℝ Θ (c t w)).det|`

## Sibling prerequisites

- `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.chart_coarea-a1.jacobian_identity-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
