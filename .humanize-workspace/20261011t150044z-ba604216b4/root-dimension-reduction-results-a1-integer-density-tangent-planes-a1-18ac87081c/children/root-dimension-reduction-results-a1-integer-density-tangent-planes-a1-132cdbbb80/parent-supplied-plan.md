# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.alpha_homogeneous-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-132cdbbb80/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1`
- Child key: `alpha_homogeneous`
- Declaration: `Submission.idtp_cse_alpha_invariant_homogeneous`
- Exact Lean type: `∀ (s : ℝ) (H : ℝ × ℝ → ℝ), 0 < s → s ≤ 1 → IntegrableOn H (Ioo (1 - s) (1 + s) ×ˢ Ioo (-s) s) → (∀ ψ l : ℝ → ℝ, ContDiff ℝ 1 ψ → ContDiff ℝ 1 l → tsupport ψ ⊆ Ioo (-s) s → tsupport l ⊆ Ioo (1 - s) (1 + s) → ∫ p : ℝ × ℝ, deriv ψ p.2 * l p.1 * H p = 0) → (∀ (l ψ : ℝ → ℝ) (r : ℝ), ContDiff ℝ 1 l → ContDiff ℝ 1 ψ → tsupport l ⊆ Ioo (1 - s / 2) (1 + s / 2) → tsupport ψ ⊆ Ioo (-s) s → |r - 1| < s / 4 → ∫ p : ℝ × ℝ, l (p.1 / r) * ψ p.2 * H p = r ^ 2 * ∫ p : ℝ × ℝ, l p.1 * ψ p.2 * H p) → ∃ c : ℝ, ∀ᵐ p : ℝ × ℝ, p ∈ Ioo (1 - s / 8) (1 + s / 8) ×ˢ Ioo (-s) s → H p = c * p.1`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
