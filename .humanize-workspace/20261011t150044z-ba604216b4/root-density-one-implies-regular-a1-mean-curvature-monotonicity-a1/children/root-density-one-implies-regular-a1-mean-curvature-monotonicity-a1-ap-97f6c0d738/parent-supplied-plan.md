# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.mean_curvature_monotonicity-a1.approx_tangent_in_tangent_space-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-mean-curvature-monotonicity-a1-ap-97f6c0d738/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.mean_curvature_monotonicity-a1`
- Child key: `approx_tangent_in_tangent_space`
- Declaration: `Submission.dsmc_approxTangentPlane_subset_tangentSpace`
- Exact Lean type: `∀ (P n r d : ℕ) (M N : Set (Euclid P)) (x : Euclid P) (Q : Submodule ℝ (Euclid P)), 1 ≤ r → IsEmbeddedSubmanifold r d N → x ∈ N → μHE[n] (M \ N) = 0 → HasApproximateTangentSpaceAt n M x Q → (Q : Set (Euclid P)) ⊆ tangentSpace N x`

## Sibling prerequisites

- `root.density_one_implies_regular-a1.mean_curvature_monotonicity-a1.chart_tangent_space-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
