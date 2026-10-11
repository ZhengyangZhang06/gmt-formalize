# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.section3_consequences-a1.chart_projection_positive-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-section3-consequences-a1-chart-projection-positive-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.section3_consequences-a1`
- Child key: `chart_projection_positive`
- Declaration: `Submission.section3_chart_coordinateProjection_pos`
- Exact Lean type: `∀ (n ℓ : ℕ) (V T : Set (Rn n)) (ψ : Rn n → Rn (n + ℓ)), IsOpen V → ContDiffOn ℝ 1 ψ V → (∀ u ∈ V, Function.Injective (fderiv ℝ ψ u)) → T ⊆ V → 0 < volume T → ∃ J : Finset (Fin (n + ℓ)), J.card = n ∧ 0 < μHE[n] (coordinateProjection J '' (ψ '' T))`

## Sibling prerequisites

- `root.section3_consequences-a1.coordinate_projection_injective-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
