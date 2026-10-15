# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.fibre_count-a1.count_arith-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-6081b9ae40/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.fibre_count-a1`
- Child key: `count_arith`
- Declaration: `Submission.idtp_cse_fc_tsum_count_arith`
- Exact Lean type: `∀ (ι : Type) (θ : ι → ℕ) (w : ι → ℝ) (t : ℝ) (m : ℕ), 0 < t → (∀ i, w i ≤ t) → ∑' i, (θ i : ℝ≥0∞) * ENNReal.ofReal (w i) = ENNReal.ofReal ((m : ℝ) * t) → (m : ℝ≥0∞) ≤ ∑' i, (θ i : ℝ≥0∞) ∧ ∀ (i₀ : ι) (k : ℕ), (∀ i, 1 ≤ θ i) → θ i₀ = k → w i₀ = t → (∀ i, i ≠ i₀ → w i < t) → k ≤ m ∧ (k < m → (m : ℝ≥0∞) + 1 ≤ ∑' i, (θ i : ℝ≥0∞))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
