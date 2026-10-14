# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.cone_class-a1.positive_scale_family-a1.domain_geometry-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-ffb81264e3/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.cone_class-a1.positive_scale_family-a1`
- Child key: `domain_geometry`
- Declaration: `Submission.idtp_fons_cc_psf_domain_geometry`
- Exact Lean type: `∀ (P : ℕ) (x : Euclid P) (lam : ℝ), 0 < lam → (∀ v : Euclid P, v ∈ dilation x lam '' ball 0 2 ↔ ‖x + lam • v‖ < 2) ∧ IsOpen (dilation x lam '' ball 0 2) ∧ (lam ≤ 1 → ‖x‖ ≤ 1 - lam → ball 0 2 ⊆ dilation x lam '' ball 0 2 ∧ ∀ R : ℝ, lam * R ≤ 1 → closedBall 0 R ⊆ dilation x lam '' ball 0 2)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
