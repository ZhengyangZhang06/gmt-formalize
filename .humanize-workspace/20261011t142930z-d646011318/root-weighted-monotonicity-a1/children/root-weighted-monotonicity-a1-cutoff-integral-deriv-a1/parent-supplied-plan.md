# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.weighted_monotonicity-a1.cutoff_integral_deriv-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-weighted-monotonicity-a1-cutoff-integral-deriv-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.weighted_monotonicity-a1`
- Child key: `cutoff_integral_deriv`
- Declaration: `Submission.weighted_mono_cutoff_hasDerivAt`
- Exact Lean type: `∀ (n ℓ : ℕ) (μ : Measure (Ambient n ℓ)) (f : Ambient n ℓ → ℝ) (φ : ℝ → ℝ) (ξ : Ambient n ℓ) (c R A τ : ℝ), IsFiniteMeasureOnCompacts μ → ContDiff ℝ 1 φ → (∀ t, c ≤ t → φ t = 0) → 0 < c → 0 < τ → c * τ < R → AEStronglyMeasurable f (μ.restrict (closedBall ξ R)) → (∀ x ∈ closedBall ξ R, |f x| ≤ A) → Integrable (fun x ↦ f x * φ (‖x - ξ‖ / τ)) μ ∧ Integrable (fun x ↦ f x * (-(‖x - ξ‖ / τ ^ 2) * deriv φ (‖x - ξ‖ / τ))) μ ∧ HasDerivAt (fun t ↦ ∫ x, f x * φ (‖x - ξ‖ / t) ∂μ) (∫ x, f x * (-(‖x - ξ‖ / τ ^ 2) * deriv φ (‖x - ξ‖ / τ)) ∂μ) τ`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
