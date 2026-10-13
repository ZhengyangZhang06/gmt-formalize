# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.lipschitz_approximation-a1.vitali_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-c3521b0aee/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.lipschitz_approximation-a1`
- Child key: `vitali_bound`
- Declaration: `Submission.dorag_lip_vitali_two_measure_bound`
- Exact Lean type: `∀ (P : ℕ) (μ ν : Measure (Euclid P)) (A B : Set (Euclid P)) (r : Euclid P → ℝ) (R₀ : ℝ) (c : ℝ≥0∞), (∀ y ∈ A, 0 < r y ∧ r y ≤ R₀ ∧ closedBall y (r y) ⊆ B ∧ μ (A ∩ closedBall y (5 * r y)) ≤ c * ν (closedBall y (r y))) → μ A ≤ c * ν B`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
