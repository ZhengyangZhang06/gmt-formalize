# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.tilt_excess_decay-a1.lp_monotonicity-a1.fixed_cutoff_monotone-a1.cutoff_mass_derivative-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-decay-a1-lp-monotonicity-a1-fixed-cutoff-monotone-a1-d08fa2abc9/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.tilt_excess_decay-a1.lp_monotonicity-a1.fixed_cutoff_monotone-a1`
- Child key: `cutoff_mass_derivative`
- Declaration: `Submission.ted_lpm_fcm_cutoff_mass_hasDerivAt`
- Exact Lean type: `∀ (n ℓ : ℕ) (μ : Measure (Amb n ℓ)) (y : Amb n ℓ) (φ : ℝ → ℝ) (S T t : ℝ), 0 < T → μ (closedBall y S) < ⊤ → ContDiff ℝ 1 φ → (∀ u : ℝ, T ≤ u → φ u = 0) → 0 < t → T * t < S → Integrable (fun x => φ (‖x - y‖ / t)) μ ∧ Integrable (fun x => ‖x - y‖ / t * deriv φ (‖x - y‖ / t)) μ ∧ HasDerivAt (fun s => ∫ x, φ (‖x - y‖ / s) ∂μ) (-(∫ x, ‖x - y‖ / t * deriv φ (‖x - y‖ / t) ∂μ) / t) t`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
