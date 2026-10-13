# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.box_mass_limits-a1.tilt_decay-a1.cutoff_form-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-c8a21b22a3/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.box_mass_limits-a1.tilt_decay-a1`
- Child key: `cutoff_form`
- Declaration: `Submission.idtp_cse_bml_td_cutoff_test_form`
- Exact Lean type: `∀ (P n : ℕ) (r : ℝ) (β : Covector (Euclid P) n), 0 < r → ∃ (ϑ : Euclid P → ℝ) (ω : TestFormOn (univ : Set (Euclid P)) n), Continuous ϑ ∧ HasCompactSupport ϑ ∧ (∀ x, 0 ≤ ϑ x ∧ ϑ x ≤ 1) ∧ (∀ x : Euclid P, ‖x‖ < r → ϑ x = 1) ∧ ∀ x, (ω : DifferentialForm (Euclid P) n) x = ϑ x • β`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
