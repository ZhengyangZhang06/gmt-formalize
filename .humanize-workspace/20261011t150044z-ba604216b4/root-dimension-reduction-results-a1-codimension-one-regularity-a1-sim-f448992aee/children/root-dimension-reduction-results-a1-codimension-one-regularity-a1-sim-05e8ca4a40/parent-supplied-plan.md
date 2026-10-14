# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.area_comparison-a1.image_submanifold-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-sim-05e8ca4a40/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.area_comparison-a1`
- Child key: `image_submanifold`
- Declaration: `Submission.codim1_ac_diffeo_image_submanifold`
- Exact Lean type: `∀ (P d : ℕ) (N : Set (Euclid P)) (Φ : Euclid P → Euclid P) (Λ : NNReal), IsEmbeddedSubmanifold 1 d N → ContDiff ℝ 1 Φ → Bijective Φ → (∀ x, Injective (fderiv ℝ Φ x)) → AntilipschitzWith Λ Φ → IsEmbeddedSubmanifold 1 d (Φ '' N) ∧ ∀ x ∈ N, tangentSpace (Φ '' N) (Φ x) = (fderiv ℝ Φ x) '' tangentSpace N x`

## Sibling prerequisites

- `root.minimizing_implies_stationary-a1.chart_tangent_space-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
