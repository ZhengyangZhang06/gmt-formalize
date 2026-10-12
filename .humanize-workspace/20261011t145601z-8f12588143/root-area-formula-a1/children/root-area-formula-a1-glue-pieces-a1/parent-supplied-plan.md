# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.area_formula-a1.glue_pieces-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-area-formula-a1-glue-pieces-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.area_formula-a1`
- Child key: `glue_pieces`
- Declaration: `Submission.areaFormula_glue_pieces`
- Exact Lean type: `∀ (X Y : Type) [MeasurableSpace X] [MeasurableSpace Y] (μ : Measure X) (ν : Measure Y) (f : X → Y) (g h : X → ℝ≥0∞) (M : Set X) (G : ℕ → Set X), NullMeasurableSet M μ → (∀ α, NullMeasurableSet (G α) μ) → μ (M \ ⋃ α, G α) = 0 → ν (f '' (M \ ⋃ α, G α)) = 0 → (∀ α, ∀ S ⊆ M ∩ G α, NullMeasurableSet S μ → (∫⁻ x in S, g x ∂μ = ∫⁻ y, ∑' x : ↥(S ∩ f ⁻¹' {y}), h x ∂ν) ∧ AEMeasurable (fun y ↦ ∑' x : ↥(S ∩ f ⁻¹' {y}), h x) ν) → ∫⁻ x in M, g x ∂μ = ∫⁻ y, ∑' x : ↥(M ∩ f ⁻¹' {y}), h x ∂ν`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
