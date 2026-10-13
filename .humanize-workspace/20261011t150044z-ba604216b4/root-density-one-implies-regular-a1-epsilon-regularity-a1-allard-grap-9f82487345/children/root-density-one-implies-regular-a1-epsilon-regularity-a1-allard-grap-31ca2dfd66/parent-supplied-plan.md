# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.harmonic_approximation-a1.mean_value-a1.ball_of_kernel-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-31ca2dfd66/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.harmonic_approximation-a1.mean_value-a1`
- Child key: `ball_of_kernel`
- Declaration: `Submission.dorag_ha_mv_ball_of_kernel`
- Exact Lean type: `∀ (n : ℕ) (h : Euclid n → ℝ) (x : Euclid n) (r : ℝ), 0 < r → ContinuousOn h (closedBall x r) → (∀ g : ℝ → ℝ, Continuous g → (∀ t : ℝ, r ^ 2 ≤ t → g t = 0) → ∫ y : Euclid n, h (x - y) * g (‖y‖ ^ 2) = h x * ∫ y : Euclid n, g (‖y‖ ^ 2)) → ∫ y in ball x r, h y = (volume (ball x r)).toReal * h x`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
