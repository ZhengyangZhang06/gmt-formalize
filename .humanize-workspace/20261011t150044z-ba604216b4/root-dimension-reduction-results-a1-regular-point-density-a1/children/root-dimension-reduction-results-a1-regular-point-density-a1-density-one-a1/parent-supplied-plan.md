# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.regular_point_density-a1.density_one-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-regular-point-density-a1-density-one-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.regular_point_density-a1`
- Child key: `density_one`
- Declaration: `Submission.dimred_rpd_submanifold_density_one`
- Exact Lean type: `∀ (P n : ℕ) (M : Set (Euclid P)) (z : Euclid P), IsEmbeddedSubmanifold 1 n M → z ∈ M → Tendsto (fun s : ℝ => μHE[n] (M ∩ ball z s) / (unitBallVolume n * ENNReal.ofReal (s ^ n))) (𝓝[>] 0) (𝓝 1)`

## Sibling prerequisites

- `root.dimension_reduction_results-a1.regular_point_density-a1.near_isometric_chart-a1`
- `root.dimension_reduction_results-a1.regular_point_density-a1.bilipschitz_measure-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
