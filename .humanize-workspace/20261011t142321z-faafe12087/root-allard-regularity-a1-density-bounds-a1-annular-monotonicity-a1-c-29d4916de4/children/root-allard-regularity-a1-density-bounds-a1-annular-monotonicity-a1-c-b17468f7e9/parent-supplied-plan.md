# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.allard_regularity-a1.density_bounds-a1.annular_monotonicity-a1.cutoff_calculus-a1.cutoff_derivative-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-regularity-a1-density-bounds-a1-annular-monotonicity-a1-c-b17468f7e9/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.allard_regularity-a1.density_bounds-a1.annular_monotonicity-a1.cutoff_calculus-a1`
- Child key: `cutoff_derivative`
- Declaration: `Submission.allard52_am_cc_cutoff_integral_hasDerivAt`
- Exact Lean type: `∀ (n ℓ : ℕ) (μ : Measure (Amb n ℓ)) (y : Amb n ℓ) (f : Amb n ℓ → ℝ) (φ : ℝ → ℝ) (S T t : ℝ), IntegrableOn f (closedBall y S) μ → ContDiff ℝ 1 φ → 0 < T → (∀ u : ℝ, T ≤ u → φ u = 0) → 0 < t → T * t < S → HasDerivAt (fun s => ∫ x, φ (‖x - y‖ / s) * f x ∂μ) (-(∫ x, ‖x - y‖ / t * deriv φ (‖x - y‖ / t) * f x ∂μ) / t) t`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
