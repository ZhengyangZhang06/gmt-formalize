# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.tangent_structure-a1.piece_tangent_field-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-tangent-structure-a1-piece-tangent-field-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.tangent_structure-a1`
- Child key: `piece_tangent_field`
- Declaration: `Submission.ts_piece_tangent_projection_field`
- Exact Lean type: `∀ (n ℓ : ℕ) (C : ℕ → Set (EuclideanSpace ℝ (Fin n))) (F : ℕ → EuclideanSpace ℝ (Fin n) → Ambient n ℓ), (∀ i, IsCompact (C i) ∧ (∃ K : NNReal, LipschitzWith K (F i)) ∧ (∀ w ∈ C i, DifferentiableAt ℝ (F i) w ∧ Function.Injective (fderiv ℝ (F i) w)) ∧ ContinuousOn (fderiv ℝ (F i)) (C i) ∧ ∃ c : ℝ, 0 < c ∧ ∀ v ∈ C i, ∀ w ∈ C i, c * ‖v - w‖ ≤ ‖F i v - F i w‖) → ∃ g : Ambient n ℓ → (Ambient n ℓ →L[ℝ] Ambient n ℓ), StronglyMeasurable g ∧ ∀ i, ∀ w ∈ C i, (∀ j < i, F i w ∉ F j '' C j) → g (F i w) = (LinearMap.range (fderiv ℝ (F i) w).toLinearMap).starProjection`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
