# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.threshold_reduction-a1.measure_class_reduction-a1.threshold_limit-a1.monotone_density-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-threshold-reduction-a1-measure-cl-52d034093f/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.threshold_reduction-a1.measure_class_reduction-a1.threshold_limit-a1`
- Child key: `monotone_density`
- Declaration: `Submission.dimred_tr_mcr_tl_monotone_density`
- Exact Lean type: `∀ (n : ℕ) (Λ R : ℝ) (m : ℝ → ℝ≥0∞), 0 < R → (∀ ρ ∈ Ioo 0 R, m ρ ≠ ∞) → MonotoneOn (fun ρ : ℝ => ENNReal.ofReal (Real.exp (Λ * ρ) / ρ ^ n) * m ρ) (Ioo 0 R) → Tendsto (fun ρ : ℝ => m ρ / (unitBallVolume n * ENNReal.ofReal (ρ ^ n))) (𝓝[>] 0) (𝓝 (ENNReal.ofReal (limsup (fun ρ : ℝ => m ρ / (unitBallVolume n * ENNReal.ofReal (ρ ^ n))) (𝓝[>] 0)).toReal)) ∧ ∀ σ ∈ Ioo 0 R, unitBallVolume n * ENNReal.ofReal (limsup (fun ρ : ℝ => m ρ / (unitBallVolume n * ENNReal.ofReal (ρ ^ n))) (𝓝[>] 0)).toReal * ENNReal.ofReal (σ ^ n * Real.exp (-(Λ * σ))) ≤ m σ`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
