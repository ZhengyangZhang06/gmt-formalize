# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.lipschitz_image_hausdorff-a1.nested_partitions-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-lipschitz-image-hausdorff-a1-nested-partitions-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.lipschitz_image_hausdorff-a1`
- Child key: `nested_partitions`
- Declaration: `Submission.lipschitzImage_exists_nested_partitions`
- Exact Lean type: `∀ (X : Type) [MetricSpace X] [TopologicalSpace.SeparableSpace X] [MeasurableSpace X] [BorelSpace X], ∃ P : ℕ → ℕ → Set X, (∀ i j, MeasurableSet (P i j)) ∧ (∀ i j k, j ≠ k → Disjoint (P i j) (P i k)) ∧ (∀ i, ⋃ j, P i j = Set.univ) ∧ (∀ i j, ∀ x ∈ P i j, ∀ x' ∈ P i j, dist x x' < 1 / ((i : ℝ) + 1)) ∧ (∀ i j, ∃ k, P (i + 1) j ⊆ P i k)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
