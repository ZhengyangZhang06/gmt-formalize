# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.harmonic_approximation-a1.rellich_ball-a1.total_bounded-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-02f7b8531e/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.harmonic_approximation-a1.rellich_ball-a1`
- Child key: `total_bounded`
- Declaration: `Submission.dorag_ha_rb_total_bounded`
- Exact Lean type: `∀ (n : ℕ) (M : ℝ) (u : ℕ → Euclid n → ℝ), (∀ j, ∃ L : NNReal, LipschitzWith L (u j)) → (∀ j, ∫ x in ball (0 : Euclid n) 1, u j x ^ 2 ≤ M) → (∀ j, ∫ x in ball (0 : Euclid n) 1, ‖fderiv ℝ (u j) x‖ ^ 2 ≤ M) → ∀ η : ℝ, 0 < η → ∃ S : Finset ℕ, ∀ j, ∃ k ∈ S, ∫ x in ball (0 : Euclid n) 1, (u j x - u k x) ^ 2 ≤ η`

## Sibling prerequisites

- `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.harmonic_approximation-a1.rellich_ball-a1.boundary_layer-a1`
- `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.harmonic_approximation-a1.rellich_ball-a1.mollify_l2-a1`
- `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.harmonic_approximation-a1.rellich_ball-a1.mollify_bounds-a1`
- `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.harmonic_approximation-a1.rellich_ball-a1.kernel-a1`
- `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.harmonic_approximation-a1.rellich_ball-a1.sup_net-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
