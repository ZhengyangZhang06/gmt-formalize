# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.coarea-a1.coarea_glue-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-ea44c4e98d/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.coarea-a1`
- Child key: `coarea_glue`
- Declaration: `Submission.dtc_bc_lc_sl_co_coarea_glue`
- Exact Lean type: `∀ (P n : ℕ) (M : Set (Euclid P)) (f : Euclid P → ℝ) (G : Euclid P → Euclid P) (A : ℕ → Set (Euclid P)), MeasurableSet M → Measurable f → (∀ j, MeasurableSet (A j)) → (∀ j, A j ⊆ M) → Pairwise (fun i j => Disjoint (A i) (A j)) → μHE[n + 1] (M \ ⋃ j, A j) = 0 → (∀ᵐ t, μHE[n] ((M \ ⋃ j, A j) ∩ f ⁻¹' {t}) = 0) → (∀ j, ∀ g : Euclid P → ℝ≥0∞, Measurable g → AEMeasurable (fun t => ∫⁻ x in A j ∩ f ⁻¹' {t}, g x ∂μHE[n]) ∧ ∫⁻ t, ∫⁻ x in A j ∩ f ⁻¹' {t}, g x ∂μHE[n] = ∫⁻ x in A j, ENNReal.ofReal ‖G x‖ * g x ∂μHE[n + 1]) → ∀ g : Euclid P → ℝ≥0∞, Measurable g → AEMeasurable (fun t => ∫⁻ x in M ∩ f ⁻¹' {t}, g x ∂μHE[n]) ∧ ∫⁻ t, ∫⁻ x in M ∩ f ⁻¹' {t}, g x ∂μHE[n] = ∫⁻ x in M, ENNReal.ofReal ‖G x‖ * g x ∂μHE[n + 1]`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
