# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.lipschitz_image_hausdorff-a1.fiber_count_sup-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-lipschitz-image-hausdorff-a1-fiber-count-sup-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.lipschitz_image_hausdorff-a1`
- Child key: `fiber_count_sup`
- Declaration: `Submission.lipschitzImage_iSup_pieceCount_eq_fiberCount`
- Exact Lean type: `∀ (X Y : Type) [MetricSpace X] (A : Set X) (f : X → Y) (P : ℕ → ℕ → Set X), (∀ i j k, j ≠ k → Disjoint (P i j) (P i k)) → (∀ i, ⋃ j, P i j = Set.univ) → (∀ i j, ∀ x ∈ P i j, ∀ x' ∈ P i j, dist x x' < 1 / ((i : ℝ) + 1)) → (∀ i j, ∃ k, P (i + 1) j ⊆ P i k) → ∀ y : Y, Monotone (fun i ↦ ∑' j, (f '' (A ∩ P i j)).indicator (1 : Y → ℝ≥0∞) y) ∧ ⨆ i, ∑' j, (f '' (A ∩ P i j)).indicator (1 : Y → ℝ≥0∞) y = fiberCount A f y`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
