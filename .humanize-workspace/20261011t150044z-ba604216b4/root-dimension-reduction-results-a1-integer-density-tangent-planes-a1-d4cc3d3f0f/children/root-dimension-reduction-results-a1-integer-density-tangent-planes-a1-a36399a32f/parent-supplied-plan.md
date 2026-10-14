# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.cone_class-a1.positive_scale_family-a1.support-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-a36399a32f/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.cone_class-a1.positive_scale_family-a1`
- Child key: `support`
- Declaration: `Submission.idtp_fons_cc_psf_support`
- Exact Lean type: `∀ (P n : ℕ) (μ μ₀ : Measure (Euclid P)) (z : Euclid P) (r : ℝ), 0 < r → μ₀ = ENNReal.ofReal (r⁻¹ ^ n) • (μ.restrict (ball z (2 * r))).map (dilation z r) → ∀ w ∈ ball (0 : Euclid P) 2, (∀ ε : ℝ, 0 < ε → μ₀ (ball w ε) ≠ 0) ↔ ∀ ε : ℝ, 0 < ε → μ (ball (z + r • w) ε) ≠ 0`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
