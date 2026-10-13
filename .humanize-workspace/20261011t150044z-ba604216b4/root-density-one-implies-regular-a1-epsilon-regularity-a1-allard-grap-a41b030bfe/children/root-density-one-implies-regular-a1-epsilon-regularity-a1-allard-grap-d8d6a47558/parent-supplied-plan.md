# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.tilt_excess_step-a1.graph_height-a1.weight_ball-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-d8d6a47558/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.tilt_excess_step-a1.graph_height-a1`
- Child key: `weight_ball`
- Declaration: `Submission.dorag_tes_gah_lipschitz_weight_ball_le`
- Exact Lean type: `∀ (n k : ℕ), 0 < n → ∀ (f : Euclid n → Euclid k), (∀ v w, ‖f v - f w‖ ≤ ‖v - w‖) → ∀ (G : Euclid n → ℝ≥0∞) (t : ℝ), (∫⁻ v in closedBall (0 : Euclid n) t, ENNReal.ofReal (1 + 2 ^ n * ∑ i : Fin n, ‖fderiv ℝ f v (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) * G v) ≤ ENNReal.ofReal (1 + n * 2 ^ n) * (∫⁻ v in ball (0 : Euclid n) t, G v)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
