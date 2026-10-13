# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.allard_any_radius-a1.graph_comparison-a1.graph_transfer-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-any-radius-a1-graph-comparison-a1-graph-transfer-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.allard_any_radius-a1.graph_comparison-a1`
- Child key: `graph_transfer`
- Declaration: `Submission.anyrad_gc_graph_lintegral_transfer`
- Exact Lean type: `∀ (n ℓ : ℕ) (q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ) (u : Rn n → Rn ℓ) (Ω : Set (Rn n)), MeasurableSet Ω → ContinuousOn u Ω → ∀ ν : Measure (Amb n ℓ), (μHE[n] : Measure (Amb n ℓ)).restrict (q '' graphOver u Ω) ≤ ν → (∀ A : Set (Rn n), MeasurableSet A → A ⊆ Ω → MeasurableSet (q '' graphOver u A)) ∧ (∀ A : Set (Rn n), MeasurableSet A → A ⊆ Ω → ∀ g : Amb n ℓ → ℝ≥0∞, Measurable g → ∫⁻ x in A, g (q (graphPoint x (u x))) ≤ ∫⁻ y in q '' graphOver u A, g y ∂ν) ∧ ∀ P : Amb n ℓ → Prop, (∀ᵐ y ∂ν, P y) → ∀ᵐ x ∂(volume.restrict Ω), P (q (graphPoint x (u x)))`

## Sibling prerequisites

- `root.allard_any_radius-a1.graph_comparison-a1.graph_volume-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
