# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.lipschitz_pieces-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-lipschitz-pieces-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root`
- Child key: `lipschitz_pieces`
- Declaration: `Submission.rectifiable_lipschitz_piece_cover`
- Exact Lean type: `∀ (n ℓ : ℕ) (M : Set (Ambient n ℓ)), 0 < n → Poincare.SimonGMT.Chapter03.CountablyRectifiable n M → ∃ (N₀ : Set (Ambient n ℓ)) (C : ℕ → Set (EuclideanSpace ℝ (Fin n))) (F : ℕ → EuclideanSpace ℝ (Fin n) → Ambient n ℓ), MeasurableSet N₀ ∧ (μHE[n] : Measure (Ambient n ℓ)) N₀ = 0 ∧ M ⊆ N₀ ∪ ⋃ i, F i '' C i ∧ ∀ i, IsCompact (C i) ∧ (∃ K : NNReal, LipschitzWith K (F i)) ∧ (∀ w ∈ C i, DifferentiableAt ℝ (F i) w ∧ Function.Injective (fderiv ℝ (F i) w)) ∧ ContinuousOn (fderiv ℝ (F i)) (C i) ∧ ∃ c : ℝ, 0 < c ∧ ∀ v ∈ C i, ∀ w ∈ C i, c * ‖v - w‖ ≤ ‖F i v - F i w‖`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
