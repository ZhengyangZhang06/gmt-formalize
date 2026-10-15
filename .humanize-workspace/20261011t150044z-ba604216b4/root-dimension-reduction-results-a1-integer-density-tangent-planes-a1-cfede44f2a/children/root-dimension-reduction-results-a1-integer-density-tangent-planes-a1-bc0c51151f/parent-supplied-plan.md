# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.one_dim_cones-a1.ray_action-a1.action_split-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-bc0c51151f/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.one_dim_cones-a1.ray_action-a1`
- Child key: `action_split`
- Declaration: `Submission.idtp_fons_odc_ra_action_split`
- Exact Lean type: `∀ (P : ℕ) (R : IMRep (univ : Set (Euclid P)) 1) (F : Finset (Euclid P)), (∀ e ∈ F, ‖e‖ = 1) → (μHE[1] : Measure (Euclid P)) (R.carrier ∩ (⋃ e ∈ F, (fun t : ℝ => t • e) '' Ioi 0)ᶜ) = 0 → ∀ ω : TestFormOn (univ : Set (Euclid P)) 1, R.action (ω : DifferentialForm (Euclid P) 1) = ∑ e ∈ F, ∫ x in R.carrier ∩ (fun t : ℝ => t • e) '' Ioi 0, (R.mult x : ℝ) * R.orient x ((ω : DifferentialForm (Euclid P) 1) x) ∂μHE[1]`

## Sibling prerequisites

- `root.regular_components_are_minimizing-a1.restriction_integer_multiplicity-a1.action_integrable-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
