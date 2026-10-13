# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_point_tangent_plane-a1.planar_support_eq-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-8c5c890e10/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_point_tangent_plane-a1`
- Child key: `planar_support_eq`
- Declaration: `Submission.idtp_tpf_planar_support_eq`
- Exact Lean type: `∀ (P n : ℕ) (C : GeometricCurrentOn (univ : Set (Euclid P)) n) (τ : Fin n → Euclid P), 1 ≤ n → Orthonormal ℝ τ → IsIntegerMultiplicity C → BoundaryVanishes C → C.support ⊆ (Submodule.span ℝ (Set.range τ) : Set (Euclid P)) → (∃ W : Set (Euclid P), IsOpen W ∧ C.massOn W ≠ 0) → C.support = (Submodule.span ℝ (Set.range τ) : Set (Euclid P))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
