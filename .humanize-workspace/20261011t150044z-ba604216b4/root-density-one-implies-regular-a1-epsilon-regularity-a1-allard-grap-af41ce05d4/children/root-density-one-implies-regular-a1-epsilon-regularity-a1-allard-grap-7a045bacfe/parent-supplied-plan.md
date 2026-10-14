# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.harmonic_approximation-a1.rellich_ball-a1.mollify_bounds-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-7a045bacfe/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.harmonic_approximation-a1.rellich_ball-a1`
- Child key: `mollify_bounds`
- Declaration: `Submission.dorag_ha_rb_mollify_bounds`
- Exact Lean type: `∀ (n : ℕ) (u ρ : Euclid n → ℝ) (C ε s : ℝ), Continuous u → Continuous ρ → (∀ z : Euclid n, 1 ≤ ‖z‖ → ρ z = 0) → (∀ z, |ρ z| ≤ C) → (∀ z z', |ρ z - ρ z'| ≤ C * ‖z - z'‖) → 0 < ε → ε ≤ s / 2 → (∀ x ∈ closedBall (0 : Euclid n) (1 - s), |∫ z, u (x - ε • z) * ρ z| ≤ (ε ^ n)⁻¹ * C * ∫ y in ball (0 : Euclid n) 1, |u y|) ∧ ∀ x ∈ closedBall (0 : Euclid n) (1 - s), ∀ x' ∈ closedBall (0 : Euclid n) (1 - s), |(∫ z, u (x - ε • z) * ρ z) - ∫ z, u (x' - ε • z) * ρ z| ≤ (ε ^ (n + 1))⁻¹ * C * ‖x - x'‖ * ∫ y in ball (0 : Euclid n) 1, |u y|`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
