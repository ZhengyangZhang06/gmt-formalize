# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.zero_scale_limit_plane-a1.graph_chart-a1.oriented_frame-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-zer-0a4283d2e3/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.zero_scale_limit_plane-a1.graph_chart-a1`
- Child key: `oriented_frame`
- Declaration: `Submission.codim1_zsl_gc_oriented_frame`
- Exact Lean type: `∀ (n k : ℕ) (Q : Submodule ℝ (Euclid (n + 1 + k))) (ξ : MultiVector (n + 1 + k) (n + 1)), IsUnitOrientationOf ξ Q → ∃ (ι : Euclid (n + 1) →ₗᵢ[ℝ] Euclid (n + 1 + k)) (ι' : Euclid k →ₗᵢ[ℝ] Euclid (n + 1 + k)), (∀ v w, inner ℝ (ι v) (ι' w) = 0) ∧ (∀ y : Euclid (n + 1 + k), ∃ v w, y = ι v + ι' w) ∧ Set.range ι = (Q : Set (Euclid (n + 1 + k))) ∧ ∀ α : Covector (Euclid (n + 1 + k)) (n + 1), ξ α = α (fun j => ι (EuclideanSpace.single j (1 : ℝ)))`

## Sibling prerequisites

- `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.lipschitz_approximation-a1.coordinates-a1`
- `root.regular_set_dense-a1.integer_combination-a1.orientation_sign-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
