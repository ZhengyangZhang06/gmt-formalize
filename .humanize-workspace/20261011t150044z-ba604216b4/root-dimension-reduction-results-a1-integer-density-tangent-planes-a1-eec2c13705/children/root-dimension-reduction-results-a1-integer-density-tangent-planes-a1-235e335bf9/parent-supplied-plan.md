# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.two_dim_cone_density-a1.planes_union_vertex_density-a1.planar_piece_measure-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-235e335bf9/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.two_dim_cone_density-a1.planes_union_vertex_density-a1`
- Child key: `planar_piece_measure`
- Declaration: `Submission.idtp_tdc_puvd_planar_piece_measure`
- Exact Lean type: `∀ (P n : ℕ) (C : GeometricCurrentOn (univ : Set (Euclid P)) n) (R : IMRep (univ : Set (Euclid P)) n) (V : Set (Euclid P)) (Q : Submodule ℝ (Euclid P)), 1 ≤ n → IsOpen V → BoundaryVanishes C → R.Represents C → Module.finrank ℝ Q = n → IsConnected (V ∩ (Q : Set (Euclid P))) → C.support ∩ V ⊆ (Q : Set (Euclid P)) → ∃ c : ℕ, ∀ E : Set (Euclid P), MeasurableSet E → E ⊆ V → R.measure E = (c : ℝ≥0∞) * μHE[n] (E ∩ (Q : Set (Euclid P)))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
