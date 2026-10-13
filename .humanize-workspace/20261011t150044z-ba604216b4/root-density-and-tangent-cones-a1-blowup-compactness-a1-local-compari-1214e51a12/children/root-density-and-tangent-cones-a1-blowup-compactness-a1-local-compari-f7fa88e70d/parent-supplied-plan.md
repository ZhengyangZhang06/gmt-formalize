# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.slice_family-a1.coarea_signed-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-f7fa88e70d/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.slice_family-a1`
- Child key: `coarea_signed`
- Declaration: `Submission.dtc_bc_lc_sl_sf_coarea_signed`
- Exact Lean type: `∀ (P n : ℕ) (M : Set (Euclid P)) (f : Euclid P → ℝ) (G : Euclid P → Euclid P), MeasurableSet M → Measurable f → Measurable G → (∀ g : Euclid P → ℝ≥0∞, Measurable g → AEMeasurable (fun t => ∫⁻ x in M ∩ f ⁻¹' {t}, g x ∂μHE[n]) ∧ ∫⁻ t, ∫⁻ x in M ∩ f ⁻¹' {t}, g x ∂μHE[n] = ∫⁻ x in M, ENNReal.ofReal ‖G x‖ * g x ∂μHE[n + 1]) → ∀ q : Euclid P → ℝ, Measurable q → ∫⁻ x in M, ENNReal.ofReal ‖G x‖ * ENNReal.ofReal |q x| ∂μHE[n + 1] ≠ ∞ → (∀ᵐ t, IntegrableOn q (M ∩ f ⁻¹' {t}) μHE[n]) ∧ Integrable (fun t => ∫ x in M ∩ f ⁻¹' {t}, q x ∂μHE[n]) ∧ ∫ t, ∫ x in M ∩ f ⁻¹' {t}, q x ∂μHE[n] = ∫ x in M, ‖G x‖ * q x ∂μHE[n + 1]`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
