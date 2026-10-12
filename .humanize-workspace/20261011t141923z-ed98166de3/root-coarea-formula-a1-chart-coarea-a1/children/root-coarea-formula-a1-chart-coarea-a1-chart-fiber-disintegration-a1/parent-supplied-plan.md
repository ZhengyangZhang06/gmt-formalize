# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.coarea_formula-a1.chart_coarea-a1.chart_fiber_disintegration-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-coarea-formula-a1-chart-coarea-a1-chart-fiber-disintegration-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.coarea_formula-a1.chart_coarea-a1`
- Child key: `chart_fiber_disintegration`
- Declaration: `Submission.coarea_chart_fiber_disintegration`
- Exact Lean type: `∀ (N m k : ℕ) (f : Rn N → Rn m) (Ω : Set (WithLp 2 (Rn m × Rn k))) (Ψ : WithLp 2 (Rn m × Rn k) → Rn N) (S : Set (Rn N)) (g : Rn N → ℝ≥0∞), IsOpen Ω → ContDiffOn ℝ 1 Ψ Ω → InjOn Ψ Ω → (∀ p ∈ Ω, Function.Injective (fderiv ℝ Ψ p)) → (∀ p ∈ Ω, f (Ψ p) = WithLp.fst p) → MeasurableSet S → S ⊆ Ψ '' Ω → Measurable g → Measurable (fun y ↦ ∫⁻ x in S ∩ f ⁻¹' {y}, g x ∂μHE[k]) ∧ ∫⁻ p in Ω ∩ Ψ ⁻¹' S, ENNReal.ofReal (((fderiv ℝ Ψ p).comp ((WithLp.prodContinuousLinearEquiv 2 ℝ (Rn m) (Rn k)).symm.toContinuousLinearMap.comp (ContinuousLinearMap.inr ℝ (Rn m) (Rn k)))).toLinearMap.normDet) * g (Ψ p) = ∫⁻ y, ∫⁻ x in S ∩ f ⁻¹' {y}, g x ∂μHE[k] ∂volume`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
