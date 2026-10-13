# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_higher_regularity-a1.c1_graph_density-a1.graph_mass_pinching-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-higher-regularity-a1-c1-graph-density-a1-graph-mass-pinching-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_higher_regularity-a1.c1_graph_density-a1`
- Child key: `graph_mass_pinching`
- Declaration: `Submission.dohr_c1_graph_mass_pinching`
- Exact Lean type: `∀ n ℓ : ℕ, 1 ≤ n → ∀ (R : ℝ) (u : Rn n → Rn ℓ), ContDiffOn ℝ 1 u (ball 0 R) → ∀ x ∈ ball (0 : Rn n) R, ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ η : ℝ, 0 < η ∧ ∀ r : ℝ, 0 < r → r ≤ η → ENNReal.ofReal ((1 - ε) ^ n / (1 + ε) ^ n * (unitBallVolume n * r ^ n)) ≤ (μHE[n] : Measure (Amb n ℓ)) (graphOver u (ball 0 R) ∩ closedBall (graphPoint x (u x)) r) ∧ (μHE[n] : Measure (Amb n ℓ)) (graphOver u (ball 0 R) ∩ closedBall (graphPoint x (u x)) r) ≤ ENNReal.ofReal ((1 + ε) ^ n / (1 - ε) ^ n * (unitBallVolume n * r ^ n))`

## Sibling prerequisites

- `root.regular_set_open_dense-a1.density_of_approx_tangent-a1.plane_ball_measure-a1`
- `root.density_one_higher_regularity-a1.c1_graph_density-a1.c1_first_order-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
