# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.cone_class-a1.monotonicity_bounds-a1.monotone_lower_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-11d84149c6/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.cone_class-a1.monotonicity_bounds-a1`
- Child key: `monotone_lower_bound`
- Declaration: `Submission.idtp_fons_cc_mb_monotone_lower_bound`
- Exact Lean type: `∀ (n : ℕ) (Λ ρ σ θ : ℝ) (m : ℝ → ℝ≥0∞), 1 ≤ θ → 0 < σ → σ < ρ → MonotoneOn (fun τ : ℝ => ENNReal.ofReal (Real.exp (Λ * τ) / τ ^ n) * m τ) (Ioo 0 ρ) → Tendsto (fun τ : ℝ => m τ / (unitBallVolume n * ENNReal.ofReal (τ ^ n))) (𝓝[>] 0) (𝓝 (ENNReal.ofReal θ)) → ENNReal.ofReal (Real.exp (-(Λ * σ))) * (unitBallVolume n * ENNReal.ofReal (σ ^ n)) ≤ m σ`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
