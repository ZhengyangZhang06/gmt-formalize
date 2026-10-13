# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.allard_regularity-a1.density_bounds-a1.annular_monotonicity-a1.fixed_cutoff-a1.lp_scale-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-regularity-a1-density-bounds-a1-annular-monotonicity-a1-f-3d4532a62f/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.allard_regularity-a1.density_bounds-a1.annular_monotonicity-a1.fixed_cutoff-a1`
- Child key: `lp_scale`
- Declaration: `Submission.allard52_am_fc_lp_scale`
- Exact Lean type: `∀ (n ℓ : ℕ) (p : ℝ), (n : ℝ) < p → ∀ (μ : Measure (Amb n ℓ)) (H : Amb n ℓ → Amb n ℓ) (y : Amb n ℓ) (R Λ t : ℝ), 0 < R → 0 < Λ → t ≤ R → (ENNReal.ofReal (R ^ (p - n)) * ∫⁻ x in closedBall y R, ‖H x‖ₑ ^ p ∂μ) ^ (1 / p) ≤ ENNReal.ofReal ((p - n) / (4 * p) * Λ) → ∫⁻ x in closedBall y t, ‖H x‖ₑ ^ p ∂μ < ⊤ ∧ (∫⁻ x in closedBall y t, ‖H x‖ₑ ^ p ∂μ).toReal ^ (1 / p) ≤ (p - n) / (4 * p) * Λ * R ^ ((n : ℝ) / p - 1)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
