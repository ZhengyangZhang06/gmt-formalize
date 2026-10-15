# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.two_dim_cone_density-a1.arc_continuation-a1.real_induction-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-c6264abf71/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.two_dim_cone_density-a1.arc_continuation-a1`
- Child key: `real_induction`
- Declaration: `Submission.idtp_tdc_acont_real_induction`
- Exact Lean type: `∀ (G : ℝ → Prop) (L : ℝ), G 0 → (∀ φ : ℝ, 0 ≤ φ → φ < L → G φ → ∃ ε : ℝ, 0 < ε ∧ ∀ ψ : ℝ, φ < ψ → ψ < φ + ε → G ψ) → (∀ φ : ℝ, 0 < φ → φ < L → (∀ ψ : ℝ, 0 ≤ ψ → ψ < φ → G ψ) → G φ) → ∀ φ : ℝ, 0 ≤ φ → φ < L → G φ`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
