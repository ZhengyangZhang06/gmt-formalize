# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.coarea-a1.slice_glue-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-6c12cf5116/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.coarea-a1`
- Child key: `slice_glue`
- Declaration: `Submission.dtc_bc_lc_sl_co_slice_glue`
- Exact Lean type: `∀ (P n : ℕ) (M : Set (Euclid P)) (f : Euclid P → ℝ) (G : Euclid P → Euclid P) (T : Euclid P → Submodule ℝ (Euclid P)) (A : ℕ → Set (Euclid P)) (L : NNReal), MeasurableSet M → Measurable f → (∀ K : Set (Euclid P), IsCompact K → μHE[n + 1] (M ∩ K) ≠ ∞) → (∀ x, ‖G x‖ ≤ L) → (∀ g : Euclid P → ℝ≥0∞, Measurable g → AEMeasurable (fun t => ∫⁻ x in M ∩ f ⁻¹' {t}, g x ∂μHE[n]) ∧ ∫⁻ t, ∫⁻ x in M ∩ f ⁻¹' {t}, g x ∂μHE[n] = ∫⁻ x in M, ENNReal.ofReal ‖G x‖ * g x ∂μHE[n + 1]) → (∀ j, MeasurableSet (A j)) → (∀ j, A j ⊆ M) → (∀ᵐ t, μHE[n] ((M \ ⋃ j, A j) ∩ f ⁻¹' {t}) = 0) → (∀ j, ∀ᵐ t, CountablyRectifiable n (A j ∩ f ⁻¹' {t}) ∧ ∀ᵐ x ∂(μHE[n].restrict (A j ∩ f ⁻¹' {t})), G x ≠ 0 ∧ HasApproximateTangentSpaceAt n (A j ∩ f ⁻¹' {t}) x (T x ⊓ (ℝ ∙ G x)ᗮ)) → ∀ᵐ t, CountablyRectifiable n (M ∩ f ⁻¹' {t}) ∧ ∀ᵐ x ∂(μHE[n].restrict (M ∩ f ⁻¹' {t})), G x ≠ 0 ∧ HasApproximateTangentSpaceAt n (M ∩ f ⁻¹' {t}) x (T x ⊓ (ℝ ∙ G x)ᗮ)`

## Sibling prerequisites

- `root.compactness_of_minimizing_currents-a1.im_calculus-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
