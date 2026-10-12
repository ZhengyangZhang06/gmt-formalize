# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.first_rectifiability-a1.weight_eq_theta_hausdorff-a1.lebesgue_density_subset-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-first-rectifiability-a1-weight-eq-theta-hausdorff-a1-lebesgue-de-11e35949fb/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.first_rectifiability-a1.weight_eq_theta_hausdorff-a1`
- Child key: `lebesgue_density_subset`
- Declaration: `Submission.frt_weq_nondensity_points_null`
- Exact Lean type: `∀ (N : ℕ) (μ : Measure (Euclidean N)) (W A : Set (Euclidean N)), IsOpen W → μ W ≠ ∞ → A ⊆ W → μ {x | x ∈ A ∧ ¬ Tendsto (fun r : ℝ => μ (A ∩ closedBall x r) / μ (closedBall x r)) (𝓝[>] 0) (𝓝 1)} = 0`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
