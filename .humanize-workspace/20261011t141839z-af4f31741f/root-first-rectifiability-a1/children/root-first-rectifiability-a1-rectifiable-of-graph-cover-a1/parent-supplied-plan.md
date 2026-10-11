# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.first_rectifiability-a1.rectifiable_of_graph_cover-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-first-rectifiability-a1-rectifiable-of-graph-cover-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.first_rectifiability-a1`
- Child key: `rectifiable_of_graph_cover`
- Declaration: `Submission.frt_countablyRectifiable_of_graph_cover`
- Exact Lean type: `∀ (N n : ℕ) (M : Set (Euclidean N)) (C : Set (Grassmannian N n × Set (Euclidean N))), C.Countable → (∀ c ∈ C, ∀ y ∈ c.2, ∀ z ∈ c.2, ‖(y - z) - Grassmannian.project c.1 (y - z)‖ ≤ ‖Grassmannian.project c.1 (y - z)‖) → M ⊆ ⋃ c ∈ C, c.2 → Chapter03.CountablyRectifiable n M`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
