# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.de_giorgi-a1.density_estimates-a1.sobolev_indicator-a1.mollified_fderiv_le-a1.fubini_swap-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-de-giorgi-a1-density-estimates-a1-sobolev-indicator-a1-mollified-18feb4c5b3/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.de_giorgi-a1.density_estimates-a1.sobolev_indicator-a1.mollified_fderiv_le-a1`
- Child key: `fubini_swap`
- Declaration: `Submission.deGiorgiSobIndMFL_integral_mul_swap`
- Exact Lean type: `∀ (N : ℕ) (μ : Measure (Rn N)) (ζ ρ : Rn N → ℝ) (r : ℝ), Continuous ζ → HasCompactSupport ζ → Continuous ρ → HasCompactSupport ρ → tsupport ρ ⊆ Metric.closedBall (0 : Rn N) r → μ (Metric.cthickening r (tsupport ζ)) < ∞ → Integrable (fun y ↦ ζ y * (∫ z, ρ (y - z) ∂μ)) ∧ ∫ y, ζ y * (∫ z, ρ (y - z) ∂μ) = ∫ z, (∫ y, ζ y * ρ (y - z)) ∂μ`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
