# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.edge_tangent_plane-a1.plane_imrep-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-376d7ec57f/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.edge_tangent_plane-a1`
- Child key: `plane_imrep`
- Declaration: `Submission.idtp_cse_etp_plane_imrep`
- Exact Lean type: `∀ (P n : ℕ) (τ : Fin n → Euclid P) (c : ℤ), Orthonormal ℝ τ → c ≠ 0 → ∃ R : IMRep (univ : Set (Euclid P)) n, (∀ ω : DifferentialForm (Euclid P) n, R.action ω = (c : ℝ) * ∫ x in (Submodule.span ℝ (Set.range τ) : Set (Euclid P)), ω x τ ∂μHE[n]) ∧ R.measure = (c.natAbs : ℝ≥0∞) • (μHE[n] : Measure (Euclid P)).restrict (Submodule.span ℝ (Set.range τ) : Set (Euclid P))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
