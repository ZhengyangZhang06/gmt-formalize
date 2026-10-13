# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.allard_regularity-a1.density_bounds-a1.annular_monotonicity-a1.fixed_cutoff-a1.radial_split-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-regularity-a1-density-bounds-a1-annular-monotonicity-a1-f-d541012eb9/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.allard_regularity-a1.density_bounds-a1.annular_monotonicity-a1.fixed_cutoff-a1`
- Child key: `radial_split`
- Declaration: `Submission.allard52_am_fc_radial_split`
- Exact Lean type: `∀ (n ℓ : ℕ) (μ : Measure (Amb n ℓ)) (w : Amb n ℓ → ℝ) (y : Amb n ℓ) (R ε : ℝ) (φ : ℝ → ℝ), 0 < ε → μ (closedBall y R) < ⊤ → AEStronglyMeasurable w (μ.restrict (ball y R)) → (∀ᵐ x ∂μ, x ∈ ball y R → 0 ≤ w x ∧ w x ≤ 1) → ContDiff ℝ 1 φ → Antitone φ → (∀ u : ℝ, u ≤ 1 → φ u = 1) → (∀ u : ℝ, 1 + ε ≤ u → φ u = 0) → ∀ t : ℝ, 0 < t → (1 + ε) * t < R → ∫ x, ((n : ℝ) * φ (‖x - y‖ / t) + ‖x - y‖ / t * deriv φ (‖x - y‖ / t) * (1 - w x)) ∂μ = (n : ℝ) * ∫ x, φ (‖x - y‖ / t) ∂μ + ∫ x, ‖x - y‖ / t * deriv φ (‖x - y‖ / t) ∂μ - ∫ x, ‖x - y‖ / t * deriv φ (‖x - y‖ / t) * w x ∂μ ∧ 0 ≤ ∫ x, φ (‖x - y‖ / t) ∂μ ∧ ∫ x, ‖x - y‖ / t * deriv φ (‖x - y‖ / t) * w x ∂μ ≤ 0`

## Sibling prerequisites

- `root.allard_regularity-a1.density_bounds-a1.annular_monotonicity-a1.fixed_cutoff-a1.cutoff_facts-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
