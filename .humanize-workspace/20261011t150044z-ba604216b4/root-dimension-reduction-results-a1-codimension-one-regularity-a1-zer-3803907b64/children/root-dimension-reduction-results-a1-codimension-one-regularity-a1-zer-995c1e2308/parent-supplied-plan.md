# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.zero_scale_limit_plane-a1.graph_chart-a1.graph_cylinder-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-zer-995c1e2308/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.zero_scale_limit_plane-a1.graph_chart-a1`
- Child key: `graph_cylinder`
- Declaration: `Submission.codim1_zsl_gc_graph_cylinder`
- Exact Lean type: `∀ (d k : ℕ) (N : Set (Euclid (d + k))) (x : Euclid (d + k)) (ι : Euclid d →ₗᵢ[ℝ] Euclid (d + k)) (ι' : Euclid k →ₗᵢ[ℝ] Euclid (d + k)) (O : Set (Euclid d)) (u : Euclid d → Euclid k) (s : ℝ), (∀ v w, inner ℝ (ι v) (ι' w) = 0) → IsOpen O → (0 : Euclid d) ∈ O → ContinuousAt u 0 → u 0 = 0 → 0 < s → (∀ v ∈ O, x + ι v + ι' (u v) ∈ N) → (∀ y ∈ N, dist y x < s → ∃ v ∈ O, y = x + ι v + ι' (u v)) → ∃ δ₁ δ₂ : ℝ, 0 < δ₁ ∧ 0 < δ₂ ∧ ball (0 : Euclid d) δ₁ ⊆ O ∧ (∀ v ∈ ball (0 : Euclid d) δ₁, u v ∈ ball (0 : Euclid k) δ₂) ∧ N ∩ {y | ∃ v ∈ ball (0 : Euclid d) δ₁, ∃ w ∈ ball (0 : Euclid k) δ₂, y = x + ι v + ι' w} = (fun v => x + ι v + ι' (u v)) '' ball (0 : Euclid d) δ₁`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
