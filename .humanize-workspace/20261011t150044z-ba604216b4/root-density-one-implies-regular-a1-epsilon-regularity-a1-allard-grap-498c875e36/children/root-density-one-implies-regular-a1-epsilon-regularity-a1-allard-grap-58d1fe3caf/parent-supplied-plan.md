# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.density_bounds-a1.constants-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-58d1fe3caf/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.density_bounds-a1`
- Child key: `constants`
- Declaration: `Submission.dorag_dbs_density_constants`
- Exact Lean type: `∀ n : ℕ, ∃ δ₁ C₁ : ℝ, 0 < δ₁ ∧ δ₁ ≤ 1 / 8 ∧ 0 < C₁ ∧ C₁ * δ₁ ≤ 1 / 2 ∧ ∀ δ : ℝ, 0 ≤ δ → δ ≤ δ₁ → Real.exp δ * (1 + δ) / (1 - 4 * δ) ^ n ≤ 1 + C₁ * δ`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
