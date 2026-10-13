# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.chart_coarea-a1.flat_fubini-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-5890810a32/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.chart_coarea-a1`
- Child key: `flat_fubini`
- Declaration: `Submission.dtc_bc_lc_sl_cc_flat_fubini`
- Exact Lean type: `∀ (n : ℕ) (c : ℝ → Euclid n → Euclid (n + 1)) (Ω Y' : Set (Euclid (n + 1))) (Θ : Euclid (n + 1) → Euclid (n + 1)) (f : Euclid (n + 1) → ℝ≥0∞), (∀ s w, c s w 0 = s ∧ ∀ i : Fin n, c s w i.succ = w i) → IsOpen Ω → ContDiffOn ℝ 1 Θ Ω → InjOn Θ Ω → Measurable f → MeasurableSet Y' → Y' ⊆ Θ '' Ω → Measurable (fun t => ∫⁻ w, (Ω ∩ Θ ⁻¹' Y').indicator (fun z => ENNReal.ofReal |(fderiv ℝ Θ z).det| * f (Θ z)) (c t w)) ∧ ∫⁻ t, ∫⁻ w, (Ω ∩ Θ ⁻¹' Y').indicator (fun z => ENNReal.ofReal |(fderiv ℝ Θ z).det| * f (Θ z)) (c t w) = ∫⁻ y in Y', f y`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
