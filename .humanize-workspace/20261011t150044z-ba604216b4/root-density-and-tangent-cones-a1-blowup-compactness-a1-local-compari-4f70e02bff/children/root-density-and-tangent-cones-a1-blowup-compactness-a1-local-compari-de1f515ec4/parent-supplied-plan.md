# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.chart_coarea-a1.jacobian_identity-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-de1f515ec4/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.chart_coarea-a1`
- Child key: `jacobian_identity`
- Declaration: `Submission.dtc_bc_lc_sl_cc_jacobian_identity`
- Exact Lean type: `∀ (n P : ℕ) (A : Euclid (n + 1) →L[ℝ] Euclid P) (ℓ : Euclid (n + 1) →L[ℝ] ℝ) (v : Euclid P) (D : Euclid (n + 1) →L[ℝ] Euclid (n + 1)) (ι : Euclid n →L[ℝ] Euclid (n + 1)), Injective A → v ∈ LinearMap.range (A : Euclid (n + 1) →ₗ[ℝ] Euclid P) → (∀ e, inner ℝ v (A e) = ℓ e) → Injective D → (∀ z, ℓ (D z) = z 0) → (∀ w, ι w 0 = 0 ∧ ∀ i : Fin n, ι w i.succ = w i) → Injective (A ∘L D ∘L ι) ∧ LinearMap.range ((A ∘L D ∘L ι : Euclid n →L[ℝ] Euclid P) : Euclid n →ₗ[ℝ] Euclid P) = LinearMap.range (A : Euclid (n + 1) →ₗ[ℝ] Euclid P) ⊓ (ℝ ∙ v)ᗮ ∧ Real.sqrt (((A ∘L D ∘L ι).adjoint ∘L (A ∘L D ∘L ι)).det) = ‖v‖ * Real.sqrt ((A.adjoint ∘L A).det) * |D.det|`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
