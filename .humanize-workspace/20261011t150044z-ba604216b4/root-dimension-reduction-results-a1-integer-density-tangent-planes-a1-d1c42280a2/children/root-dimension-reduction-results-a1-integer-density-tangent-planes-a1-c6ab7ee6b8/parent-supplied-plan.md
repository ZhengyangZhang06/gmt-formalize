# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.two_dim_cone_density-a1.arc_continuation-a1.great_circle-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-c6ab7ee6b8/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.two_dim_cone_density-a1.arc_continuation-a1`
- Child key: `great_circle`
- Declaration: `Submission.idtp_tdc_acont_great_circle`
- Exact Lean type: `∀ (P : ℕ) (z e : Euclid P), ‖z‖ = 1 → ‖e‖ = 1 → inner ℝ z e = 0 → (∀ φ : ℝ, ‖Real.cos φ • z + Real.sin φ • e‖ = 1) ∧ (∀ φ ψ : ℝ, ‖(Real.cos φ • z + Real.sin φ • e) - (Real.cos ψ • z + Real.sin ψ • e)‖ ≤ |φ - ψ|) ∧ ∀ φ : ℝ, ‖Real.sin φ • z - Real.cos φ • e‖ = 1 ∧ inner ℝ (Real.cos φ • z + Real.sin φ • e) (Real.sin φ • z - Real.cos φ • e) = 0 ∧ ∀ ψ : ℝ, Real.cos ψ • (Real.cos φ • z + Real.sin φ • e) + Real.sin ψ • (Real.sin φ • z - Real.cos φ • e) = Real.cos (φ - ψ) • z + Real.sin (φ - ψ) • e`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
