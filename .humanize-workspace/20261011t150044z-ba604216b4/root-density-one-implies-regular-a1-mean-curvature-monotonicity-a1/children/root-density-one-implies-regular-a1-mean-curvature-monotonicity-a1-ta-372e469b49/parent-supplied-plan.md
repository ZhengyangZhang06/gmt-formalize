# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.mean_curvature_monotonicity-a1.tangent_projection_field-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-mean-curvature-monotonicity-a1-ta-372e469b49/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.mean_curvature_monotonicity-a1`
- Child key: `tangent_projection_field`
- Declaration: `Submission.dsmc_tangent_projection_field`
- Exact Lean type: `∀ (P d : ℕ) (U N : Set (Euclid P)) (y₀ : Euclid P), IsOpen U → IsEmbeddedSubmanifold 2 d N → y₀ ∈ N ∩ U → ∃ (r β : ℝ) (Pt : Euclid P → (Euclid P →L[ℝ] Euclid P)), 0 < r ∧ 0 ≤ β ∧ closedBall y₀ (3 * r) ⊆ U ∧ ContDiffOn ℝ 1 Pt (ball y₀ (3 * r)) ∧ (∀ y ∈ ball y₀ (3 * r), ∀ u w : Euclid P, inner ℝ (Pt y u) w = inner ℝ u (Pt y w)) ∧ (∀ y ∈ ball y₀ (2 * r), ‖fderiv ℝ Pt y‖ ≤ β) ∧ (∀ q ∈ N ∩ ball y₀ (3 * r), ∀ u : Euclid P, Pt q u ∈ tangentSpace N q) ∧ (∀ q ∈ N ∩ ball y₀ (3 * r), ∀ u ∈ tangentSpace N q, Pt q u = u)`

## Sibling prerequisites

- `root.density_one_implies_regular-a1.mean_curvature_monotonicity-a1.chart_tangent_space-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
