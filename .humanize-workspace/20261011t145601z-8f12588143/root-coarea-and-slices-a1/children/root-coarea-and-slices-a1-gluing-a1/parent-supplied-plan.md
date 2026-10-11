# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.coarea_and_slices-a1.gluing-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-coarea-and-slices-a1-gluing-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.coarea_and_slices-a1`
- Child key: `gluing`
- Declaration: `Submission.coarea_gluing_of_pieces`
- Exact Lean type: `∀ (N n m k : ℕ) (U M : Set (Rn N)) (f : Rn N → Rn m) (w : Rn N → ℝ≥0∞) (S : ℕ → Set (Rn N)), IsOpen U → M ⊆ U → ContinuousOn f U → (∀ Z ⊆ M, μHE[n] Z = 0 → ∀ᵐ y ∂(volume : Measure (Rn m)), μHE[k] (Z ∩ f ⁻¹' {y}) = 0) → (∀ j, MeasurableSet (S j)) → μHE[n] (M \ ⋃ j, S j) = 0 → (∀ j, ∀ B ⊆ S j, MeasurableSet B → ∀ φ : Rn N → ℝ≥0∞, Measurable φ → AEMeasurable (fun y : Rn m ↦ ∫⁻ x in B ∩ f ⁻¹' {y}, φ x ∂μHE[k]) volume ∧ ∫⁻ x in B, φ x * w x ∂μHE[n] = ∫⁻ y, (∫⁻ x in B ∩ f ⁻¹' {y}, φ x ∂μHE[k]) ∂volume) → ∀ A ⊆ M, NullMeasurableSet A μHE[n] → ∀ g : Rn N → ℝ≥0∞, AEMeasurable g ((μHE[n] : Measure (Rn N)).restrict A) → ∫⁻ x in A, g x * w x ∂μHE[n] = ∫⁻ y, (∫⁻ x in A ∩ f ⁻¹' {y}, g x ∂μHE[k]) ∂volume`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
