# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.planar_constancy-a1.plane_measure_map-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-ca4a690a2b/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.planar_constancy-a1`
- Child key: `plane_measure_map`
- Declaration: `Submission.idtp_pc_plane_hausdorff_eq_map`
- Exact Lean type: `∀ (P n : ℕ) (τ : Fin n → Euclid P), Orthonormal ℝ τ → (μHE[n] : Measure (Euclid P)).restrict (Submodule.span ℝ (Set.range τ) : Set (Euclid P)) = Measure.map (fun s : Euclid n => ∑ i, s i • τ i) volume`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
