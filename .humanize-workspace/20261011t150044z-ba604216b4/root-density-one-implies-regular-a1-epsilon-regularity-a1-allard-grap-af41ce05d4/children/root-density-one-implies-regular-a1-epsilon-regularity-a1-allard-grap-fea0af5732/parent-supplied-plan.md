# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.harmonic_approximation-a1.rellich_ball-a1.dilation_average-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-fea0af5732/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.harmonic_approximation-a1.rellich_ball-a1`
- Child key: `dilation_average`
- Declaration: `Submission.dorag_ha_rb_dilation_average`
- Exact Lean type: `∀ (n : ℕ) (F : Euclid n → ℝ) (s : ℝ), Measurable F → (∀ y, 0 ≤ F y) → IntegrableOn F (ball (0 : Euclid n) 1) → 0 < s → s ≤ 1 / 2 → ∫ x in ball (0 : Euclid n) 1 \ ball (0 : Euclid n) (1 - s), (∫ t in (1 / 2 : ℝ)..1, F (t • x)) ≤ 2 ^ (n + 1) * s * ∫ y in ball (0 : Euclid n) 1, F y`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
