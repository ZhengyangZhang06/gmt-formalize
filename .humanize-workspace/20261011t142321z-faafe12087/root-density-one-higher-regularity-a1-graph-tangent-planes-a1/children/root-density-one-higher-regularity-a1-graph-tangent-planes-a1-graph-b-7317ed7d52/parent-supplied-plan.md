# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_higher_regularity-a1.graph_tangent_planes-a1.graph_ball_growth-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-higher-regularity-a1-graph-tangent-planes-a1-graph-b-7317ed7d52/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_higher_regularity-a1.graph_tangent_planes-a1`
- Child key: `graph_ball_growth`
- Declaration: `Submission.dohr_tp_graph_ball_growth`
- Exact Lean type: `∀ n ℓ : ℕ, 1 ≤ n → ∀ (R ρ : ℝ) (u : Rn n → Rn ℓ), 0 < ρ → ρ < R → ContDiffOn ℝ 1 u (ball 0 R) → ∃ C : ℝ, 0 ≤ C ∧ ∀ (z : Amb n ℓ) (r : ℝ), 0 < r → (μHE[n] : Measure (Amb n ℓ)) (graphOver u (ball 0 ρ) ∩ closedBall z r) ≤ ENNReal.ofReal (C * r ^ n)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
