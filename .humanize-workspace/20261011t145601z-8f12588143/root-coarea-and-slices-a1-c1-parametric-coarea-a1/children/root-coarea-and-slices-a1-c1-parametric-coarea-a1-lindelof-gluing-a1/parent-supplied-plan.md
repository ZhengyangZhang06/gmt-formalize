# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.coarea_and_slices-a1.c1_parametric_coarea-a1.lindelof_gluing-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-coarea-and-slices-a1-c1-parametric-coarea-a1-lindelof-gluing-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.coarea_and_slices-a1.c1_parametric_coarea-a1`
- Child key: `lindelof_gluing`
- Declaration: `Submission.pcoarea_gluing`
- Exact Lean type: `∀ (n N m k : ℕ) (D Z : Set (Rn n)) (ψ : Rn n → Rn N) (G : Rn n → Rn m) (w : Rn n → ℝ≥0∞), IsOpen D → ContinuousOn ψ D → InjOn ψ D → Continuous G → (∀ B ⊆ D, MeasurableSet B → B ⊆ Z → ∀ φ : Rn N → ℝ≥0∞, Measurable φ → AEMeasurable (fun y : Rn m ↦ ∫⁻ x in ψ '' (B ∩ G ⁻¹' {y}), φ x ∂μHE[k]) volume ∧ ∫⁻ u in B, φ (ψ u) * w u = ∫⁻ y, (∫⁻ x in ψ '' (B ∩ G ⁻¹' {y}), φ x ∂μHE[k]) ∂volume) → (∀ p ∈ D, p ∉ Z → ∃ O : Set (Rn n), IsOpen O ∧ p ∈ O ∧ ∀ B ⊆ D ∩ O, MeasurableSet B → ∀ φ : Rn N → ℝ≥0∞, Measurable φ → AEMeasurable (fun y : Rn m ↦ ∫⁻ x in ψ '' (B ∩ G ⁻¹' {y}), φ x ∂μHE[k]) volume ∧ ∫⁻ u in B, φ (ψ u) * w u = ∫⁻ y, (∫⁻ x in ψ '' (B ∩ G ⁻¹' {y}), φ x ∂μHE[k]) ∂volume) → ∀ B ⊆ D, MeasurableSet B → ∀ φ : Rn N → ℝ≥0∞, Measurable φ → AEMeasurable (fun y : Rn m ↦ ∫⁻ x in ψ '' (B ∩ G ⁻¹' {y}), φ x ∂μHE[k]) volume ∧ ∫⁻ u in B, φ (ψ u) * w u = ∫⁻ y, (∫⁻ x in ψ '' (B ∩ G ⁻¹' {y}), φ x ∂μHE[k]) ∂volume`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
