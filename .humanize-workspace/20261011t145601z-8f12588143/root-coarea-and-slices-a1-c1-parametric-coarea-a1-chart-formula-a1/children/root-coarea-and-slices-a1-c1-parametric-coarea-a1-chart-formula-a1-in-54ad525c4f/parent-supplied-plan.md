# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.coarea_and_slices-a1.c1_parametric_coarea-a1.chart_formula-a1.integrand_tonelli-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-coarea-and-slices-a1-c1-parametric-coarea-a1-chart-formula-a1-in-54ad525c4f/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.coarea_and_slices-a1.c1_parametric_coarea-a1.chart_formula-a1`
- Child key: `integrand_tonelli`
- Declaration: `Submission.pcoarea_chart_integrand_tonelli`
- Exact Lean type: `∀ (m k N : ℕ) (ψ : Rn (m + k) → Rn N) (Φ : OpenPartialHomeomorph (Rn (m + k)) (WithLp 2 (Rn m × Rn k))), ContinuousOn ψ Φ.source → ∀ B ⊆ Φ.source, MeasurableSet B → ∀ φ : Rn N → ℝ≥0∞, Measurable φ → Measurable (fun y : Rn m ↦ ∫⁻ z : Rn k, (Φ '' B).indicator (fun w ↦ φ (ψ (Φ.symm w)) * ENNReal.ofReal (((fderiv ℝ (ψ ∘ Φ.symm) w).comp ((WithLp.prodContinuousLinearEquiv 2 ℝ (Rn m) (Rn k)).symm.toContinuousLinearMap.comp (ContinuousLinearMap.inr ℝ (Rn m) (Rn k)))).toLinearMap.normDet)) (WithLp.toLp 2 (y, z))) ∧ ∫⁻ w, (Φ '' B).indicator (fun w ↦ φ (ψ (Φ.symm w)) * ENNReal.ofReal (((fderiv ℝ (ψ ∘ Φ.symm) w).comp ((WithLp.prodContinuousLinearEquiv 2 ℝ (Rn m) (Rn k)).symm.toContinuousLinearMap.comp (ContinuousLinearMap.inr ℝ (Rn m) (Rn k)))).toLinearMap.normDet)) w = ∫⁻ y : Rn m, ∫⁻ z : Rn k, (Φ '' B).indicator (fun w ↦ φ (ψ (Φ.symm w)) * ENNReal.ofReal (((fderiv ℝ (ψ ∘ Φ.symm) w).comp ((WithLp.prodContinuousLinearEquiv 2 ℝ (Rn m) (Rn k)).symm.toContinuousLinearMap.comp (ContinuousLinearMap.inr ℝ (Rn m) (Rn k)))).toLinearMap.normDet)) (WithLp.toLp 2 (y, z))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
