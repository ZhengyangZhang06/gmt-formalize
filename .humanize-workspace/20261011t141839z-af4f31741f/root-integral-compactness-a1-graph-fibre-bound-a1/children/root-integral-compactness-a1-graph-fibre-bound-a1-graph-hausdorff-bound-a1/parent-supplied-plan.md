# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.integral_compactness-a1.graph_fibre_bound-a1.graph_hausdorff_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-integral-compactness-a1-graph-fibre-bound-a1-graph-hausdorff-bound-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.integral_compactness-a1.graph_fibre_bound-a1`
- Child key: `graph_hausdorff_bound`
- Declaration: `Submission.intcpt_graph_hausdorff_le_projection`
- Exact Lean type: `∀ (N n : ℕ) (P : Grassmannian N n) (L : ℝ) (A : Set (Euclidean N)), 0 ≤ L → (∀ y ∈ A, ∀ z ∈ A, ‖(y - z) - Grassmannian.project P (y - z)‖ ≤ L * ‖Grassmannian.project P (y - z)‖) → (μHE[n] : Measure (Euclidean N)) A ≤ ENNReal.ofReal ((1 + L ^ 2) ^ ((n : ℝ) / 2)) * (μHE[n] : Measure (Euclidean N)) (Grassmannian.project P '' A)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
