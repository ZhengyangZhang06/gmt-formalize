# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.de_giorgi-a1.tangent_measure-a1.c1_to_cc_extension-a1.ball_integral_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-de-giorgi-a1-tangent-measure-a1-c1-to-cc-extension-a1-ball-integ-c57bf04e7d/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.de_giorgi-a1.tangent_measure-a1.c1_to_cc_extension-a1`
- Child key: `ball_integral_bound`
- Declaration: `Submission.deGiorgiTM_integral_bound_of_ball`
- Exact Lean type: `∀ (N : ℕ) (ν : Measure (Rn N)) (a : Rn N) (ρ M : ℝ) (g : Rn N → ℝ), ν (Metric.ball a ρ) < ∞ → Continuous g → (∀ y, |g y| ≤ M) → (∀ y, g y ≠ 0 → y ∈ Metric.ball a ρ) → Integrable g ν ∧ |∫ y, g y ∂ν| ≤ M * ν.real (Metric.ball a ρ)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
