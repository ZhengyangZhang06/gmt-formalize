# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.tangent_graph_cover-a1.cone_graph_cover-a1.local_graph_closed_cover-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-tangent-graph-cover-a1-cone-graph-cover-a1-local-graph-closed-cover-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.tangent_graph_cover-a1.cone_graph_cover-a1`
- Child key: `local_graph_closed_cover`
- Declaration: `Submission.tgc_local_graph_closed_cover`
- Exact Lean type: `∀ (N n : ℕ) (L r : ℝ) (P : Grassmannian N n) (E : Set (Euclidean N)), 0 < r → (∀ y ∈ E, ∀ z ∈ E, ‖y - z‖ ≤ r → ‖(y - z) - Grassmannian.project P (y - z)‖ ≤ L * ‖Grassmannian.project P (y - z)‖) → ∃ Γ : ℕ → Set (Euclidean N), (∀ i, IsClosed (Γ i)) ∧ (∀ i, ∀ y ∈ Γ i, ∀ z ∈ Γ i, ‖(y - z) - Grassmannian.project P (y - z)‖ ≤ L * ‖Grassmannian.project P (y - z)‖) ∧ ∀ x ∈ E, ∃ i, x ∈ Γ i`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
