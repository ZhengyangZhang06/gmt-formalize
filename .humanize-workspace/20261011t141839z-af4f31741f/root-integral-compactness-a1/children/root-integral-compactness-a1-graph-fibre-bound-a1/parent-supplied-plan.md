# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.integral_compactness-a1.graph_fibre_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-integral-compactness-a1-graph-fibre-bound-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.integral_compactness-a1`
- Child key: `graph_fibre_bound`
- Declaration: `Submission.intcpt_lipschitz_graph_fibre_bound`
- Exact Lean type: `∀ (N n : ℕ) (P : Grassmannian N n) (L : ℝ) (Γ : ℕ → Set (Euclidean N)) (G : Set (Euclidean N)) (g : Euclidean N → ℝ≥0∞), 0 ≤ L → (∀ i, IsClosed (Γ i)) → (∀ i, ∀ y ∈ Γ i, ∀ z ∈ Γ i, ‖(y - z) - Grassmannian.project P (y - z)‖ ≤ L * ‖Grassmannian.project P (y - z)‖) → G ⊆ ⋃ i, Γ i → NullMeasurableSet G (μHE[n] : Measure (Euclidean N)) → ∫⁻ y in G, g y ∂(μHE[n] : Measure (Euclidean N)) ≤ ENNReal.ofReal ((1 + L ^ 2) ^ ((n : ℝ) / 2)) * ∫⁻ a in (P.plane : Set (Euclidean N)), (∑' y : {y : Euclidean N // y ∈ G ∧ Grassmannian.project P y = a}, g y) ∂(μHE[n] : Measure (Euclidean N))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
