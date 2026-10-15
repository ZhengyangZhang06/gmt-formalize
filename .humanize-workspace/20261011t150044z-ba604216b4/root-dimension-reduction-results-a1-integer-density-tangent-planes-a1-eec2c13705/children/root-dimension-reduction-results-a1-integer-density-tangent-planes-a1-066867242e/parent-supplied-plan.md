# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.two_dim_cone_density-a1.planes_union_vertex_density-a1.measure_sum_planes-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-066867242e/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.two_dim_cone_density-a1.planes_union_vertex_density-a1`
- Child key: `measure_sum_planes`
- Declaration: `Submission.idtp_tdc_puvd_measure_eq_sum_planes`
- Exact Lean type: `∀ (P n q : ℕ) (C : GeometricCurrentOn (univ : Set (Euclid P)) n) (R : IMRep (univ : Set (Euclid P)) n) (Ps : Fin q → Submodule ℝ (Euclid P)), 1 ≤ n → R.Represents C → (∀ i j, i ≠ j → Ps i ⊓ Ps j = ⊥) → (∀ x ∈ C.support, x ≠ 0 → ∃ i, x ∈ Ps i) → ∀ A : Set (Euclid P), MeasurableSet A → R.measure A = ∑ i, R.measure (A ∩ ((Ps i : Set (Euclid P)) \ {0}))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
