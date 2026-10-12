# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.harmonic_approximation-a1.rellich_ball-a1.boundary_layer-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-5dd9644db8/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.harmonic_approximation-a1.rellich_ball-a1`
- Child key: `boundary_layer`
- Declaration: `Submission.dorag_ha_rb_boundary_layer`
- Exact Lean type: `∀ (n : ℕ) (u : Euclid n → ℝ) (L : NNReal) (s : ℝ), LipschitzWith L u → 0 < s → s ≤ 1 / 2 → ∫ x in ball (0 : Euclid n) 1 \ ball (0 : Euclid n) (1 - s), u x ^ 2 ≤ 2 ^ (n + 3) * s * ((∫ x in ball (0 : Euclid n) 1, u x ^ 2) + ∫ x in ball (0 : Euclid n) 1, ‖fderiv ℝ u x‖ ^ 2)`

## Sibling prerequisites

- `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.harmonic_approximation-a1.rellich_ball-a1.ray_ftc-a1`
- `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.harmonic_approximation-a1.rellich_ball-a1.dilation_average-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
