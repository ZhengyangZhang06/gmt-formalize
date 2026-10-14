# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.rectifiable_density_one-a1.ae_approx_tangent-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-9c3aed61c9/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.rectifiable_density_one-a1`
- Child key: `ae_approx_tangent`
- Declaration: `Submission.codim1_rdo_rectifiable_ae_approxTangent`
- Exact Lean type: `∀ (P n : ℕ) (M : Set (Euclid P)), MeasurableSet M → CountablyRectifiable n M → (∀ K : Set (Euclid P), IsCompact K → μHE[n] (M ∩ K) ≠ ∞) → ∀ᵐ w ∂(μHE[n].restrict M), ∃ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n M w Q`

## Sibling prerequisites

- `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.rectifiable_density_one-a1.c1_cover-a1`
- `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.rectifiable_density_one-a1.c1_piece_tangent-a1`
- `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.graph_tangent-a1.tangent_transfer-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
