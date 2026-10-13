# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.graph_chart-a1.unit_orientation_isometry-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-98cf693311/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.graph_chart-a1`
- Child key: `unit_orientation_isometry`
- Declaration: `Submission.codim1_rdo_gc_unitOrientation_isometry`
- Exact Lean type: `∀ (P m : ℕ) (ξ : MultiVector P (m + 1)) (Q : Submodule ℝ (Euclid P)), IsUnitOrientationOf ξ Q → ∃ ι : Euclid (m + 1) →ₗᵢ[ℝ] Euclid P, Set.range ι = (Q : Set (Euclid P)) ∧ ∀ α : Covector (Euclid P) (m + 1), ξ α = α (fun i => ι (EuclideanSpace.single i 1))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
