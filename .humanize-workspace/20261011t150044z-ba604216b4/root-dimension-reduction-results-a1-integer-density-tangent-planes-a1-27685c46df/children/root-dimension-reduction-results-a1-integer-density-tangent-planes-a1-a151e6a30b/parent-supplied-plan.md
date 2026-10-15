# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.flux_density-a1.identify_constant-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-a151e6a30b/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.flux_density-a1`
- Child key: `identify_constant`
- Declaration: `Submission.idtp_cse_fd_identify_constant`
- Exact Lean type: `∀ (s c : ℝ) (m : ℕ) (H : ℝ × ℝ → ℝ≥0∞) (I : ℝ → ℝ≥0∞), 0 < s → s ≤ 1 → (∀ᵐ p : ℝ × ℝ, H p ≠ ∞) → (∀ᵐ p : ℝ × ℝ, p ∈ Ioo (1 - s / 8) (1 + s / 8) ×ˢ Ioo (-s) s → (H p).toReal = c * p.1) → (∀ s' : ℝ, 0 < s' → s' ≤ s / 8 → ∫⁻ p in Ioo (1 - s') (1 + s') ×ˢ Ioo (-s') s', H p = I s') → Tendsto (fun s' : ℝ => I s' / ENNReal.ofReal (s' ^ 2)) (𝓝[>] 0) (𝓝 (4 * (m : ℝ≥0∞))) → ∀ᵐ p : ℝ × ℝ, p ∈ Ioo (1 - s / 8) (1 + s / 8) ×ˢ Ioo (-(s / 8)) (s / 8) → H p = ENNReal.ofReal ((m : ℝ) * p.1)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
