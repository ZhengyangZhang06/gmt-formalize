# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.harmonic_approximation-a1.energy_lsc-a1.exhaustion-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-f87091675c/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.harmonic_approximation-a1.energy_lsc-a1`
- Child key: `exhaustion`
- Declaration: `Submission.dorag_ha_lsc_exhaustion`
- Exact Lean type: `∀ (n : ℕ) (R E : ℝ) (f : Euclid n → ℝ), 0 < R → ContinuousOn f (ball (0 : Euclid n) R) → (∀ x ∈ ball (0 : Euclid n) R, 0 ≤ f x) → (∀ r, 0 < r → r < R → ∫ x in ball (0 : Euclid n) r, f x ≤ E) → IntegrableOn f (ball (0 : Euclid n) R) ∧ ∫ x in ball (0 : Euclid n) R, f x ≤ E`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
