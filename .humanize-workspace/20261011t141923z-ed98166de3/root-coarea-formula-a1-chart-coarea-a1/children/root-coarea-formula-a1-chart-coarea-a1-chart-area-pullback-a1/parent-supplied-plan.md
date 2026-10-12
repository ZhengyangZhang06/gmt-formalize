# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.coarea_formula-a1.chart_coarea-a1.chart_area_pullback-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-coarea-formula-a1-chart-coarea-a1-chart-area-pullback-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.coarea_formula-a1.chart_coarea-a1`
- Child key: `chart_area_pullback`
- Declaration: `Submission.coarea_chart_area_pullback`
- Exact Lean type: `∀ (N m k : ℕ) (M : Set (Rn N)) (f : Rn N → Rn m) (Ω : Set (WithLp 2 (Rn m × Rn k))) (Ψ : WithLp 2 (Rn m × Rn k) → Rn N) (S : Set (Rn N)) (g : Rn N → ℝ≥0∞), IsOpen Ω → ContDiffOn ℝ 1 Ψ Ω → InjOn Ψ Ω → (∀ p ∈ Ω, Function.Injective (fderiv ℝ Ψ p)) → (∀ p ∈ Ω, DifferentiableAt ℝ f (Ψ p)) → (∀ p ∈ Ω, f (Ψ p) = WithLp.fst p) → (∀ p ∈ Ω, tangentSpace M (Ψ p) = LinearMap.range (fderiv ℝ Ψ p).toLinearMap) → MeasurableSet S → S ⊆ Ψ '' Ω → (∀ (x : Rn N) (A : WithLp 2 (Rn m × Rn k) →L[ℝ] Rn N) (B : Rn k →L[ℝ] Rn N), Function.Injective A → tangentSpace M x = LinearMap.range A.toLinearMap → (∀ p, fderiv ℝ f x (A p) = WithLp.fst p) → (∀ b, B b = A (WithLp.toLp 2 (0, b))) → coareaJacobian M f x * A.toLinearMap.normDet = B.toLinearMap.normDet) → ∫⁻ x in S, g x * ENNReal.ofReal (coareaJacobian M f x) ∂μHE[m + k] = ∫⁻ p in Ω ∩ Ψ ⁻¹' S, ENNReal.ofReal (((fderiv ℝ Ψ p).comp ((WithLp.prodContinuousLinearEquiv 2 ℝ (Rn m) (Rn k)).symm.toContinuousLinearMap.comp (ContinuousLinearMap.inr ℝ (Rn m) (Rn k)))).toLinearMap.normDet) * g (Ψ p)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
