# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.fibre_area-a1.sector_open_smooth-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-fb37424eec/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.fibre_area-a1`
- Child key: `sector_open_smooth`
- Declaration: `Submission.idtp_cse_fa_sector_open_contDiffOn`
- Exact Lean type: `∀ (P : ℕ) (Q : Submodule ℝ (Euclid P)) (a e : Euclid P) (s : ℝ), IsOpen {x : Euclid P | 0 < inner ℝ x a ∧ |‖x‖ - 1| < s ∧ |Real.arctan (inner ℝ x e / inner ℝ x a)| < s ∧ ‖x - Q.starProjection x‖ < s * ‖x‖} ∧ ContDiffOn ℝ 1 (fun x : Euclid P => (‖x‖, Real.arctan (inner ℝ x e / inner ℝ x a))) {x : Euclid P | 0 < inner ℝ x a}`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
