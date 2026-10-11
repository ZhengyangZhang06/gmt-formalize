# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.lipschitz_pieces-a1.single_map_cover-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-lipschitz-pieces-a1-single-map-cover-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.lipschitz_pieces-a1`
- Child key: `single_map_cover`
- Declaration: `Submission.lipschitz_range_piece_cover`
- Exact Lean type: `∀ (n ℓ : ℕ) (K : NNReal) (f : EuclideanSpace ℝ (Fin n) → Ambient n ℓ), LipschitzWith K f → ∃ (Y : Set (Ambient n ℓ)) (C : ℕ → Set (EuclideanSpace ℝ (Fin n))), (μHE[n] : Measure (Ambient n ℓ)) Y = 0 ∧ Set.range f ⊆ Y ∪ ⋃ i, f '' C i ∧ ∀ i, IsCompact (C i) ∧ (∀ w ∈ C i, DifferentiableAt ℝ f w ∧ Function.Injective (fderiv ℝ f w)) ∧ ContinuousOn (fderiv ℝ f) (C i) ∧ ∃ c : ℝ, 0 < c ∧ ∀ v ∈ C i, ∀ w ∈ C i, c * ‖v - w‖ ≤ ‖f v - f w‖`

## Sibling prerequisites

- `root.lipschitz_pieces-a1.regular_set_cover-a1`
- `root.lipschitz_pieces-a1.lusin_exhaustion-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
