# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.tilt_excess_decay-a1.planes_limit-a1.geometric_limit-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-a3d099e8e3/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.tilt_excess_decay-a1.planes_limit-a1`
- Child key: `geometric_limit`
- Declaration: `Submission.dorag_ted_pl_geometric_limit`
- Exact Lean type: `∀ (X : Type) [MetricSpace X] [CompleteSpace X] (v : ℕ → X) (a q : ℝ), 0 ≤ q → q ≤ 1 / 4 → (∀ j : ℕ, dist (v j) (v (j + 1)) ^ 2 ≤ a * q ^ j) → ∃ w : X, Tendsto v atTop (𝓝 w) ∧ ∀ j : ℕ, dist (v j) w ^ 2 ≤ 4 * a * q ^ j`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
