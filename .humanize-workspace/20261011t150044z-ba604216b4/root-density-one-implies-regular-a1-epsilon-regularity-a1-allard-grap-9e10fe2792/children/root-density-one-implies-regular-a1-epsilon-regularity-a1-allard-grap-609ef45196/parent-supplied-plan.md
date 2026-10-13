# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.affine_approximation-a1.height_bounds-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-609ef45196/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.affine_approximation-a1`
- Child key: `height_bounds`
- Declaration: `Submission.dorag_aa_height_bounds_of_net`
- Exact Lean type: `∀ (P : ℕ) (μ : Measure (Euclid P)) (S : Submodule ℝ (Euclid P)) (F : Finset (Euclid P)) (ξ x₀ : Euclid P) (r s L : ℝ), (∀ x ∈ μ.support ∩ closedBall ξ r, ∃ y ∈ F, dist x y ≤ s) → (∀ y ∈ F, ‖(y - x₀) - S.starProjection (y - x₀)‖ ≤ L) → dist x₀ ξ ≤ s → (∀ x ∈ μ.support ∩ closedBall ξ r, ‖(x - ξ) - S.starProjection (x - ξ)‖ ≤ 2 * s + L) ∧ ∫⁻ x in closedBall ξ r, ENNReal.ofReal (‖(x - ξ) - S.starProjection (x - ξ)‖ ^ 2) ∂μ ≤ ENNReal.ofReal ((2 * s + L) ^ 2) * μ (closedBall ξ r)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
