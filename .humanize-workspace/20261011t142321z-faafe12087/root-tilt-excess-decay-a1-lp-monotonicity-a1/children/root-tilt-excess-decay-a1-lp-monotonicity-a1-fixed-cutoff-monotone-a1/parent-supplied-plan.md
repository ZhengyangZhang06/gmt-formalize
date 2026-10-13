# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.tilt_excess_decay-a1.lp_monotonicity-a1.fixed_cutoff_monotone-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-decay-a1-lp-monotonicity-a1-fixed-cutoff-monotone-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.tilt_excess_decay-a1.lp_monotonicity-a1`
- Child key: `fixed_cutoff_monotone`
- Declaration: `Submission.ted_lpm_fixed_cutoff_monotone`
- Exact Lean type: `∀ (n ℓ : ℕ) (μ : Measure (Amb n ℓ)) (H : Amb n ℓ → Amb n ℓ) (y : Amb n ℓ) (φ : ℝ → ℝ) (I a : ℝ → ℝ) (T S M β : ℝ), 0 < T → β < 1 → μ (closedBall y S) < ⊤ → IntegrableOn H (closedBall y S) μ → ContDiff ℝ 1 φ → Antitone φ → (∀ t : ℝ, T ≤ t → φ t = 0) → (∀ ρ : ℝ, 0 < ρ → T * ρ < S → ∫ x, ((n : ℝ) * φ (‖x - y‖ / ρ) + ‖x - y‖ / ρ * deriv φ (‖x - y‖ / ρ)) ∂μ ≤ -∫ x, φ (‖x - y‖ / ρ) * inner ℝ (x - y) (H x) ∂μ) → (∀ t : ℝ, I t = ∫ x, φ (‖x - y‖ / t) ∂μ) → (∀ t : ℝ, a t = (∫ x, φ (‖x - y‖ / t) * inner ℝ (x - y) (H x) ∂μ) / t ^ (n + 1) / (1 + I t / t ^ n)) → (∀ t : ℝ, 0 < t → T * t < S → |a t| ≤ M * t ^ (-β)) → ContinuousOn a (Ioo 0 (S / T)) ∧ MonotoneOn (fun ρ => Real.exp (-∫ t in (0)..ρ, a t) * (1 + I ρ / ρ ^ n)) (Ioo 0 (S / T))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
