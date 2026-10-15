# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.cone_class-a1.cycle_rescale-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-9820912c8b/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.cone_class-a1`
- Child key: `cycle_rescale`
- Declaration: `Submission.idtp_fons_cc_cycle_rescale`
- Exact Lean type: `∀ (P n : ℕ) (S : GeometricCurrentOn (univ : Set (Euclid P)) n) (R : IMRep (univ : Set (Euclid P)) n) (y : Euclid P) (t : ℝ), 1 ≤ n → 0 < t → IsMinimizingIn S univ → BoundaryVanishes S → R.Represents S → ∃ (S' : GeometricCurrentOn (univ : Set (Euclid P)) n) (R' : IMRep (univ : Set (Euclid P)) n), IsMinimizingIn S' univ ∧ BoundaryVanishes S' ∧ R'.Represents S' ∧ R'.measure = ENNReal.ofReal (t⁻¹ ^ n) • R.measure.map (dilation y t)`

## Sibling prerequisites

- `root.density_and_tangent_cones-a1.blowup_scaling-a1`
- `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.cone_class-a1.ambient_calculus-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
