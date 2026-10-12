# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.curvature_monotonicity-a1.lp_holder_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-curvature-monotonicity-a1-lp-holder-bound-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.curvature_monotonicity-a1`
- Child key: `lp_holder_bound`
- Declaration: `Submission.mcm_lp_holder_bound`
- Exact Lean type: `∀ (n ℓ : ℕ) (μ : Measure (Ambient n ℓ)) (H : Ambient n ℓ → Ambient n ℓ) (p : ℝ) (ξ : Ambient n ℓ) (R τ : ℝ), 0 < n → IsFiniteMeasureOnCompacts μ → (n : ℝ) < p → MemLp H (ENNReal.ofReal p) (μ.restrict (closedBall ξ R)) → 0 < τ → τ ≤ R → |(∫ x in closedBall ξ τ, inner ℝ (x - ξ) (H x) ∂μ) / τ ^ (n + 1)| ≤ (R ^ (p - n) * ∫ x in closedBall ξ R, ‖H x‖ ^ p ∂μ) ^ (1 / p) / R * (τ / R) ^ (-(n : ℝ) / p) * (1 + μ.real (closedBall ξ τ) / τ ^ n)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
