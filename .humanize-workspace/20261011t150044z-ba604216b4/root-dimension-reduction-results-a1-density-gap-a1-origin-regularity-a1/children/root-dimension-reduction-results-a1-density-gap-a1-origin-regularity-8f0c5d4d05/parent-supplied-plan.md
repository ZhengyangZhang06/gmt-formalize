# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.density_gap-a1.origin_regularity-a1.cylinder_graph-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-density-gap-a1-origin-regularity-8f0c5d4d05/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.density_gap-a1.origin_regularity-a1`
- Child key: `cylinder_graph`
- Declaration: `Submission.dimred_cdg_or_ball_graph_to_cylinder_graph`
- Exact Lean type: `∀ (n k : ℕ) (S : Set (Euclid (n + k))) (ι : Euclid n →ₗᵢ[ℝ] Euclid (n + k)) (ι' : Euclid k →ₗᵢ[ℝ] Euclid (n + k)) (u : Euclid n → Euclid k) (z : Euclid (n + k)) (r : ℝ), 0 < r → (∀ v w, inner ℝ (ι v) (ι' w) = 0) → u 0 = 0 → ContDiffOn ℝ 1 u (ball 0 r) → (∀ v ∈ ball (0 : Euclid n) r, ‖fderiv ℝ u v‖ ≤ 1 / 4) → S ∩ ball z r = ((fun v => z + ι v + ι' (u v)) '' ball (0 : Euclid n) r) ∩ ball z r → S ∩ {x | ∃ v ∈ ball (0 : Euclid n) (r / 4), ∃ w ∈ ball (0 : Euclid k) (r / 4), x = z + ι v + ι' w} = (fun v => z + ι v + ι' (u v)) '' ball (0 : Euclid n) (r / 4)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
