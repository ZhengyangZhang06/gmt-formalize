# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.affine_approximation-a1.separated_net-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-1875404a59/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.affine_approximation-a1`
- Child key: `separated_net`
- Declaration: `Submission.dorag_aa_finite_separated_net`
- Exact Lean type: `∀ (P : ℕ) (μ : Measure (Euclid P)) (K A : Set (Euclid P)) (s : ℝ) (a : ℝ≥0∞), 0 < s → 0 < a → μ A ≠ ∞ → (∀ y ∈ K, closedBall y (s / 2) ⊆ A) → (∀ y ∈ K, a ≤ μ (closedBall y (s / 2))) → ∃ F : Finset (Euclid P), (↑F : Set (Euclid P)) ⊆ K ∧ (F.card : ℝ≥0∞) * a ≤ μ A ∧ ∀ x ∈ K, ∃ y ∈ F, dist x y ≤ s`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
