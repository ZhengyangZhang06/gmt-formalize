# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.coarea_and_slices-a1.c1_parametric_coarea-a1.chart_formula-a1.pointwise_jacobian-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-coarea-and-slices-a1-c1-parametric-coarea-a1-chart-formula-a1-po-5e783a3c52/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.coarea_and_slices-a1.c1_parametric_coarea-a1.chart_formula-a1`
- Child key: `pointwise_jacobian`
- Declaration: `Submission.pcoarea_chart_pointwise_jacobian`
- Exact Lean type: `∀ (m k N : ℕ) (ψ : Rn (m + k) → Rn N) (G : Rn (m + k) → Rn m) (Φ : OpenPartialHomeomorph (Rn (m + k)) (WithLp 2 (Rn m × Rn k))), ContDiffOn ℝ 1 ψ Φ.source → ContDiffOn ℝ 1 Φ Φ.source → ContDiffOn ℝ 1 Φ.symm Φ.target → (∀ u ∈ Φ.source, (Φ u).fst = G u) → (∀ (A : Rn (m + k) →ₗ[ℝ] Rn N) (Γ : Rn (m + k) →ₗ[ℝ] Rn m) (T : Rn (m + k) →ₗ[ℝ] WithLp 2 (Rn m × Rn k)) (E : Rn k →ₗ[ℝ] Rn (m + k)), Function.Bijective T → (∀ v, (T v).fst = Γ v) → (∀ z, T (E z) = WithLp.toLp 2 (0, z)) → (A ∘ₗ E).normDet * T.normDet = (A ∘ₗ (LinearMap.ker Γ).subtype).normDet * (LinearMap.adjoint Γ).normDet) → ∀ u ∈ Φ.source, ((fderiv ℝ (ψ ∘ Φ.symm) (Φ u)).comp ((WithLp.prodContinuousLinearEquiv 2 ℝ (Rn m) (Rn k)).symm.toContinuousLinearMap.comp (ContinuousLinearMap.inr ℝ (Rn m) (Rn k)))).toLinearMap.normDet * (fderiv ℝ Φ u).toLinearMap.normDet = ((fderiv ℝ ψ u).toLinearMap ∘ₗ (LinearMap.ker (fderiv ℝ G u).toLinearMap).subtype).normDet * (LinearMap.adjoint (fderiv ℝ G u).toLinearMap).normDet`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
