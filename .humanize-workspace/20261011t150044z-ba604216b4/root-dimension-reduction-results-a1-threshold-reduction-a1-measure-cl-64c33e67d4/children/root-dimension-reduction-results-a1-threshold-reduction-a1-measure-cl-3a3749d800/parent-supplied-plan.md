# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.threshold_reduction-a1.measure_class_reduction-a1.threshold_limit-a1.density_lower_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-threshold-reduction-a1-measure-cl-3a3749d800/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.threshold_reduction-a1.measure_class_reduction-a1.threshold_limit-a1`
- Child key: `density_lower_bound`
- Declaration: `Submission.dimred_tr_mcr_tl_density_lower_bound`
- Exact Lean type: `∀ (n : ℕ) (Λ c s : ℝ) (m : ℝ → ℝ≥0∞) (L : ℝ≥0∞), 0 < s → (∀ t ∈ Ioo 0 s, unitBallVolume n * ENNReal.ofReal c * ENNReal.ofReal (t ^ n * Real.exp (-(Λ * t))) ≤ m t) → Tendsto (fun t : ℝ => m t / (unitBallVolume n * ENNReal.ofReal (t ^ n))) (𝓝[>] 0) (𝓝 L) → ENNReal.ofReal c ≤ L`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
