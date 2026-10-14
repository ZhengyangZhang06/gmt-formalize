# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.harmonic_approximation-a1.poincare_ball-a1.pair_sq_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-9728bda458/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.harmonic_approximation-a1.poincare_ball-a1`
- Child key: `pair_sq_bound`
- Declaration: `Submission.dorag_ha_pb_pair_sq_bound`
- Exact Lean type: `∀ (n : ℕ) (u : Euclid n → ℝ) (L : NNReal), LipschitzWith L u → ∀ᵐ p : Euclid n × Euclid n, (u p.1 - u p.2) ^ 2 ≤ ‖p.1 - p.2‖ ^ 2 * ∫ t in (0 : ℝ)..1, ‖fderiv ℝ u ((1 - t) • p.2 + t • p.1)‖ ^ 2`

## Sibling prerequisites

- `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.harmonic_approximation-a1.poincare_ball-a1.segment_ftc-a1`
- `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.harmonic_approximation-a1.poincare_ball-a1.segment_null-a1`
- `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.harmonic_approximation-a1.poincare_ball-a1.sq_integral_le-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
