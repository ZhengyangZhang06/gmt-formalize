# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.epsilon_regularity-a1.graph_cycle_regular-a1.smooth_to_c1_tests-a1.pairing_uniform_limit-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-graph-cycle-7c9bddfc2c/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.graph_cycle_regular-a1.smooth_to_c1_tests-a1`
- Child key: `pairing_uniform_limit`
- Declaration: `Submission.dgcr_stc_setIntegral_mul_eq_zero_of_uniform_approx`
- Exact Lean type: `∀ (n : ℕ) (K : Set (Euclid n)) (G f : Euclid n → ℝ) (C : ℝ), MeasurableSet K → IntegrableOn G K volume → AEStronglyMeasurable f (volume.restrict K) → (∀ x ∈ K, |f x| ≤ C) → (∀ ε : ℝ, 0 < ε → ∃ g : Euclid n → ℝ, AEStronglyMeasurable g (volume.restrict K) ∧ (∀ x ∈ K, |f x - g x| ≤ ε) ∧ ∫ x in K, G x * g x = 0) → ∫ x in K, G x * f x = 0`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
