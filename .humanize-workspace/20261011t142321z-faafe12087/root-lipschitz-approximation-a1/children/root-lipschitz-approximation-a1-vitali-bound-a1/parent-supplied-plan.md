# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.lipschitz_approximation-a1.vitali_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-lipschitz-approximation-a1-vitali-bound-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.lipschitz_approximation-a1`
- Child key: `vitali_bound`
- Declaration: `Submission.lip_approx_vitali_bound`
- Exact Lean type: `∀ (N : ℕ) (ν Ψ : Measure (EuclideanSpace ℝ (Fin N))) (S W : Set (EuclideanSpace ℝ (Fin N))) (r : EuclideanSpace ℝ (Fin N) → ℝ) (R₀ : ℝ) (M : ℝ≥0∞), (∀ y ∈ S, 0 < r y ∧ r y ≤ R₀ ∧ closedBall y (r y) ⊆ W ∧ ν (S ∩ closedBall y (5 * r y)) ≤ M * Ψ (closedBall y (r y))) → ν S ≤ M * Ψ W`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
