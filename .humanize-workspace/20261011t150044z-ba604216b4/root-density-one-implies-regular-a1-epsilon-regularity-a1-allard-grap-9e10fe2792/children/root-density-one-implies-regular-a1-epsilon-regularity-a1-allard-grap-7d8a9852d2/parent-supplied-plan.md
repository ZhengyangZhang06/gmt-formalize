# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.affine_approximation-a1.low_height_point-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-7d8a9852d2/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.affine_approximation-a1`
- Child key: `low_height_point`
- Declaration: `Submission.dorag_aa_exists_low_height_point`
- Exact Lean type: `∀ (P m : ℕ) (μ : Measure (Euclid P)) (T : Euclid P → Submodule ℝ (Euclid P)) (Q : Euclid P → Prop) (F : Finset (Euclid P)) (ξ : Euclid P) (r s c lam : ℝ), AEStronglyMeasurable (fun x => (T x).starProjection) μ → (∀ᵐ x ∂μ, Q x) → 0 < r → s ≤ r → (∀ y ∈ F, dist y ξ ≤ r) → (∀ y ∈ F, ∫⁻ x in closedBall y (2 * r), ENNReal.ofReal (‖(x - y) - (T x).starProjection (x - y)‖ ^ 2 / ‖x - y‖ ^ m) ∂μ ≤ ENNReal.ofReal c) → (F.card : ℝ≥0∞) * ENNReal.ofReal ((2 * r) ^ m * c) < ENNReal.ofReal lam * μ (closedBall ξ s) → ∃ x₀ ∈ closedBall ξ s, Q x₀ ∧ ∀ y ∈ F, ‖(y - x₀) - (T x₀).starProjection (y - x₀)‖ ^ 2 ≤ lam`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
