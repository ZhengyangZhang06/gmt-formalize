# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.coarea_and_slices-a1.c1_parametric_coarea-a1.c1_injective_area-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-coarea-and-slices-a1-c1-parametric-coarea-a1-c1-injective-area-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.coarea_and_slices-a1.c1_parametric_coarea-a1`
- Child key: `c1_injective_area`
- Declaration: `Submission.pcoarea_c1_injOn_area_formula`
- Exact Lean type: `∀ (k N : ℕ) (V : Set (Rn k)) (χ : Rn k → Rn N), IsOpen V → ContDiffOn ℝ 1 χ V → InjOn χ V → ∀ S ⊆ V, MeasurableSet S → ∀ φ : Rn N → ℝ≥0∞, Measurable φ → ∫⁻ x in χ '' S, φ x ∂μHE[k] = ∫⁻ z in S, φ (χ z) * ENNReal.ofReal ((fderiv ℝ χ z).toLinearMap.normDet)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
