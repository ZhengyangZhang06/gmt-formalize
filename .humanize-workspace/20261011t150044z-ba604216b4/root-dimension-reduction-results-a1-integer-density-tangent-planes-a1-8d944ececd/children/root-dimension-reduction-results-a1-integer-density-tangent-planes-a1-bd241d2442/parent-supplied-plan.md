# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.one_dim_cones-a1.finite_rays-a1.cone_disjoint-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-bd241d2442/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.one_dim_cones-a1.finite_rays-a1`
- Child key: `cone_disjoint`
- Declaration: `Submission.idtp_fons_odc_fr_cone_disjoint`
- Exact Lean type: `∀ (P : ℕ) (σ σ' : Euclid P) (ρ : ℝ), ‖σ‖ = 1 → ‖σ'‖ = 1 → 0 < ρ → ρ ≤ 1 → 2 * ρ ≤ ‖σ - σ'‖ → Disjoint (⋃ (t : ℝ) (_ : 0 < t), ball (t • σ) (t * ρ)) (⋃ (s : ℝ) (_ : 0 < s), ball (s • σ') (s * ρ))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
