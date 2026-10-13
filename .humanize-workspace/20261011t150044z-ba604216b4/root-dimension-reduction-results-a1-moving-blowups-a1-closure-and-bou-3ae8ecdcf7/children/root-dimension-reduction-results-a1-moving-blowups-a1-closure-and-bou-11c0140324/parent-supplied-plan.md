# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.moving_blowups-a1.closure_and_boundary_rectifiability-a1.closure_zero-a1.point_sum_im-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-closure-and-bou-11c0140324/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.moving_blowups-a1.closure_and_boundary_rectifiability-a1.closure_zero-a1`
- Child key: `point_sum_im`
- Declaration: `Submission.dmcbrz_isIntegerMultiplicity_point_sum`
- Exact Lean type: `∀ (P : ℕ) (V : Set (Euclid P)) (S : GeometricCurrentOn V 0) (M : ℕ) (v : ℕ → ℤ) (y : ℕ → Euclid P), (∀ ω : TestFormOn V 0, S ω = ∑ l ∈ Finset.range M, (v l : ℝ) * (ω : DifferentialForm (Euclid P) 0) (y l) (fun i => i.elim0)) → IsIntegerMultiplicity S`

## Sibling prerequisites

- `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.closure_zero-a1.count_integral-a1`
- `root.dimension_reduction_results-a1.moving_blowups-a1.closure_and_boundary_rectifiability-a1.closure_zero-a1.finite_tangent-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
