# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.fibre_count-a1.square_lower-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-c9b50ab42a/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.fibre_count-a1`
- Child key: `square_lower`
- Declaration: `Submission.idtp_cse_fc_square_lintegral_lower`
- Exact Lean type: `∀ (N : ℝ × ℝ → ℝ≥0∞) (m : ℕ) (r : ℝ), 0 < r → (∀ᵐ p : ℝ × ℝ, p ∈ Ioo (1 - r) (1 + r) ×ˢ Ioo (-r) r → (m : ℝ≥0∞) ≤ N p) → (∀ᵐ p : ℝ × ℝ, p ∈ Ioo (1 - r) (1 + r) ×ˢ Ioo (-r) r → 0 < p.2 → (m : ℝ≥0∞) + 1 ≤ N p) → ENNReal.ofReal ((4 * (m : ℝ) + 2) * r ^ 2) ≤ ∫⁻ p in Ioo (1 - r) (1 + r) ×ˢ Ioo (-r) r, N p`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
