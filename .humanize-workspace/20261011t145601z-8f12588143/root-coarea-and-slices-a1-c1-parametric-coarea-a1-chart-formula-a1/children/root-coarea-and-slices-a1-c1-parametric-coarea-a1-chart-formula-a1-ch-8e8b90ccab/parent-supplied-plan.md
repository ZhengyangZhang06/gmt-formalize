# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.coarea_and_slices-a1.c1_parametric_coarea-a1.chart_formula-a1.change_of_variables-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-coarea-and-slices-a1-c1-parametric-coarea-a1-chart-formula-a1-ch-8e8b90ccab/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.coarea_and_slices-a1.c1_parametric_coarea-a1.chart_formula-a1`
- Child key: `change_of_variables`
- Declaration: `Submission.pcoarea_chart_change_of_variables`
- Exact Lean type: `∀ (m k : ℕ) (f : Rn (m + k) → WithLp 2 (Rn m × Rn k)) (f' : Rn (m + k) → Rn (m + k) →L[ℝ] WithLp 2 (Rn m × Rn k)) (B : Set (Rn (m + k))), MeasurableSet B → (∀ u ∈ B, HasFDerivWithinAt f (f' u) B u) → InjOn f B → ∀ g : WithLp 2 (Rn m × Rn k) → ℝ≥0∞, ∫⁻ w in f '' B, g w = ∫⁻ u in B, ENNReal.ofReal ((f' u).toLinearMap.normDet) * g (f u)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
