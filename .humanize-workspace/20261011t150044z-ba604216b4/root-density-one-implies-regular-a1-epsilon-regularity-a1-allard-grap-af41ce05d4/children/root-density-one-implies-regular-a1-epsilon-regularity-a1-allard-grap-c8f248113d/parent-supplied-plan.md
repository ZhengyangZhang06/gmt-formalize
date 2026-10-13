# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.harmonic_approximation-a1.rellich_ball-a1.mollify_l2-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-c8f248113d/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.harmonic_approximation-a1.rellich_ball-a1`
- Child key: `mollify_l2`
- Declaration: `Submission.dorag_ha_rb_mollify_l2`
- Exact Lean type: `∀ (n : ℕ) (u ρ : Euclid n → ℝ) (L : NNReal) (ε s : ℝ), LipschitzWith L u → Continuous ρ → (∀ z, 0 ≤ ρ z) → (∀ z : Euclid n, 1 ≤ ‖z‖ → ρ z = 0) → ∫ z, ρ z = 1 → 0 < ε → ε ≤ s → ∫ x in ball (0 : Euclid n) (1 - s), (u x - ∫ z, u (x - ε • z) * ρ z) ^ 2 ≤ ε ^ 2 * ∫ x in ball (0 : Euclid n) 1, ‖fderiv ℝ u x‖ ^ 2`

## Sibling prerequisites

- `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.harmonic_approximation-a1.rellich_ball-a1.translation_l2-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
