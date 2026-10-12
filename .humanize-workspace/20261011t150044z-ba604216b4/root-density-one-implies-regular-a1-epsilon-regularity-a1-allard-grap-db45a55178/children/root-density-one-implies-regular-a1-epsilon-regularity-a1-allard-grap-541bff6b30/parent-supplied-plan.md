# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.graph_c1-a1.graph_projection-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-541bff6b30/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.graph_c1-a1`
- Child key: `graph_projection`
- Declaration: `Submission.dorag_gc_graph_slope_le_projection`
- Exact Lean type: `∀ (n k P : ℕ) (ι : Euclid n →ₗᵢ[ℝ] Euclid P) (ι' : Euclid k →ₗᵢ[ℝ] Euclid P) (A₁ A₂ : Euclid n →L[ℝ] Euclid k), (∀ v w, inner ℝ (ι v) (ι' w) = 0) → ‖A₁‖ ≤ 1 / 4 → ‖A₂‖ ≤ 1 / 4 → ∑ i : Fin n, ‖(A₁ - A₂) (EuclideanSpace.single i (1 : ℝ))‖ ^ 2 ≤ 4 * ∑ j : Fin P, ‖(LinearMap.range (ι.toLinearMap + ι'.toLinearMap ∘ₗ A₁.toLinearMap)).starProjection (EuclideanSpace.single j (1 : ℝ)) - (LinearMap.range (ι.toLinearMap + ι'.toLinearMap ∘ₗ A₂.toLinearMap)).starProjection (EuclideanSpace.single j (1 : ℝ))‖ ^ 2`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
