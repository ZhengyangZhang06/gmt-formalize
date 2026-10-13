# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.graph_chart-a1.gram_unit_orientation-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-a571a4f1fc/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.graph_chart-a1`
- Child key: `gram_unit_orientation`
- Declaration: `Submission.codim1_rdo_gc_gram_unitOrientation`
- Exact Lean type: `∀ (P m : ℕ) (b : Fin m → Euclid P), LinearIndependent ℝ b → 0 < Matrix.det (Matrix.of fun i j => inner ℝ (b i) (b j)) ∧ ∀ ξ : MultiVector P m, (∀ α : Covector (Euclid P) m, ξ α * Real.sqrt (Matrix.det (Matrix.of fun i j => inner ℝ (b i) (b j))) = α b) → IsUnitOrientationOf ξ (Submodule.span ℝ (Set.range b))`

## Sibling prerequisites

- `root.minimizing_implies_stationary-a1.diffeo_pushforward-a1.orientation_pushforward-a1.gram_schmidt_frame-a1`
- `root.density_one_implies_regular-a1.epsilon_regularity-a1.graph_cycle_regular-a1.graph_orientation_jacobian-a1.covector_frame_det-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
