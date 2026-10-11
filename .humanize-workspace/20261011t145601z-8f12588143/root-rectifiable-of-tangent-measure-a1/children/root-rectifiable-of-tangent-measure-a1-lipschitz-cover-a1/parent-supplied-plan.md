# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.rectifiable_of_tangent_measure-a1.lipschitz_cover-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-rectifiable-of-tangent-measure-a1-lipschitz-cover-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.rectifiable_of_tangent_measure-a1`
- Child key: `lipschitz_cover`
- Declaration: `Submission.tangentMeasure_lipschitz_cover_of_projection_bound`
- Exact Lean type: `∀ (N n : ℕ) (Q : Submodule ℝ (Rn N)) (E : Set (Rn N)) (C δ : ℝ), finrank ℝ Q = n → 0 < δ → (∀ x ∈ E, ∀ y ∈ E, ‖y - x‖ < δ → ‖y - x‖ ≤ C * ‖Q.starProjection (y - x)‖) → ∃ F : ℕ → Rn n → Rn N, (∀ i, ∃ K : ℝ≥0, LipschitzWith K (F i)) ∧ E ⊆ ⋃ i, Set.range (F i)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
