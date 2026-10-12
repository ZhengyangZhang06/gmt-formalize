# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.integral_compactness-a1.allard_lemma-a1.cylinder_cluster_bound-a1.one_point_ball_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-integral-compactness-a1-allard-lemma-a1-cylinder-cluster-bound-a-b3dd689a45/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.integral_compactness-a1.allard_lemma-a1.cylinder_cluster_bound-a1`
- Child key: `one_point_ball_bound`
- Declaration: `Submission.intcpt_allard_ccb_one_point_ball_bound`
- Exact Lean type: `∀ (N n : ℕ) (μ : Measure (Euclidean N)) (x y : Euclidean N) (δ ε σ : ℝ), 0 < δ → δ ≤ 1 / 2 → 0 < ε → ε ≤ δ ^ 4 → ‖y - x‖ < ε → MonotoneOn (fun r : ℝ ↦ ENNReal.ofReal (Real.exp (ε * r)) * μ (closedBall y r) / ENNReal.ofReal r ^ n) (Ioo 0 1) → 0 < σ → σ ≤ δ ^ 2 → μ (closedBall y σ) / ENNReal.ofReal σ ^ n ≤ ENNReal.ofReal (1 + 2 ^ (n + 2) * δ ^ 2) * μ (closedBall x 1)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
