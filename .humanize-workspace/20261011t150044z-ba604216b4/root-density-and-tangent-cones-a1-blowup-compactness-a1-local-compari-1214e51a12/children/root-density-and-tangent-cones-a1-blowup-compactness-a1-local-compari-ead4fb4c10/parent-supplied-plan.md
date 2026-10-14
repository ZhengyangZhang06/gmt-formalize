# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.slice_family-a1.coarea_ae-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-ead4fb4c10/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.slice_family-a1`
- Child key: `coarea_ae`
- Declaration: `Submission.dtc_bc_lc_sl_sf_coarea_ae`
- Exact Lean type: `∀ (P n : ℕ) (M : Set (Euclid P)) (f : Euclid P → ℝ) (G : Euclid P → Euclid P), MeasurableSet M → Measurable f → Measurable G → (∀ g : Euclid P → ℝ≥0∞, Measurable g → AEMeasurable (fun t => ∫⁻ x in M ∩ f ⁻¹' {t}, g x ∂μHE[n]) ∧ ∫⁻ t, ∫⁻ x in M ∩ f ⁻¹' {t}, g x ∂μHE[n] = ∫⁻ x in M, ENNReal.ofReal ‖G x‖ * g x ∂μHE[n + 1]) → (∀ p : Euclid P → Prop, (∀ᵐ x ∂(μHE[n + 1].restrict M), p x) → ∀ᵐ t, ∀ᵐ x ∂(μHE[n].restrict (M ∩ f ⁻¹' {t})), p x) ∧ (∀ c : ℝ, ∀ᵐ x ∂(μHE[n + 1].restrict M), f x = c → G x = 0) ∧ ∀ g : Euclid P → ℝ≥0∞, Measurable g → (∀ K : Set (Euclid P), IsCompact K → ∫⁻ x in M ∩ K, ENNReal.ofReal ‖G x‖ * g x ∂μHE[n + 1] ≠ ∞) → ∀ᵐ t, ∀ K : Set (Euclid P), IsCompact K → ∫⁻ x in M ∩ f ⁻¹' {t} ∩ K, g x ∂μHE[n] ≠ ∞`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
