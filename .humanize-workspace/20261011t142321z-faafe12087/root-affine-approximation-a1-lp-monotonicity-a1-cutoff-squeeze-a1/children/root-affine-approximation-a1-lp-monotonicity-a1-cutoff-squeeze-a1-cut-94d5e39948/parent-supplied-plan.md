# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.affine_approximation-a1.lp_monotonicity-a1.cutoff_squeeze-a1.cutoff_derivative-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-affine-approximation-a1-lp-monotonicity-a1-cutoff-squeeze-a1-cut-94d5e39948/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.affine_approximation-a1.lp_monotonicity-a1.cutoff_squeeze-a1`
- Child key: `cutoff_derivative`
- Declaration: `Submission.aal_cfs_hasDerivAt_cutoff_integral`
- Exact Lean type: `∀ (n ℓ : ℕ) (μ : Measure (Amb n ℓ)) (q : Amb n ℓ → ℝ) (y : Amb n ℓ) (φ : ℝ → ℝ) (S ε B t : ℝ), 0 < ε → μ (closedBall y S) < ⊤ → AEStronglyMeasurable q μ → (∀ᵐ x ∂μ, |q x| ≤ B) → ContDiff ℝ 1 φ → Antitone φ → (∀ s : ℝ, s ≤ 1 → φ s = 1) → (∀ s : ℝ, 1 + ε ≤ s → φ s = 0) → 0 < t → (1 + ε) * t < S → Integrable (fun x => φ (‖x - y‖ / t) * q x) μ ∧ Integrable (fun x => ‖x - y‖ / t * deriv φ (‖x - y‖ / t) * q x) μ ∧ HasDerivAt (fun s => ∫ x, φ (‖x - y‖ / s) * q x ∂μ) (-(∫ x, ‖x - y‖ / t * deriv φ (‖x - y‖ / t) * q x ∂μ) / t) t`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
