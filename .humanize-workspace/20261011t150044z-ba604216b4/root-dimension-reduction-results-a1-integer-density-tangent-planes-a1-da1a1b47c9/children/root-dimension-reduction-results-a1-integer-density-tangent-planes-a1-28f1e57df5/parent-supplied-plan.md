# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.box_mass_limits-a1.square_measure-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-28f1e57df5/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.box_mass_limits-a1`
- Child key: `square_measure`
- Declaration: `Submission.idtp_cse_bml_plane_square_measure`
- Exact Lean type: `∀ (P : ℕ) (Q : Submodule ℝ (Euclid P)) (a e : Euclid P), Module.finrank ℝ Q = 2 → a ∈ Q → e ∈ Q → ‖a‖ = 1 → ‖e‖ = 1 → inner ℝ a e = 0 → IsFiniteMeasureOnCompacts (μHE[2].restrict (Q : Set (Euclid P))) ∧ ∀ r : ℝ, 0 ≤ r → r ≤ 2 → μHE[2].restrict (Q : Set (Euclid P)) {w : Euclid P | ‖w‖ < 3 ∧ |inner ℝ w a| < r ∧ |inner ℝ w e| < r} = ENNReal.ofReal (4 * r ^ 2) ∧ μHE[2].restrict (Q : Set (Euclid P)) {w : Euclid P | ‖w‖ ≤ 3 ∧ |inner ℝ w a| ≤ r ∧ |inner ℝ w e| ≤ r} = ENNReal.ofReal (4 * r ^ 2)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
