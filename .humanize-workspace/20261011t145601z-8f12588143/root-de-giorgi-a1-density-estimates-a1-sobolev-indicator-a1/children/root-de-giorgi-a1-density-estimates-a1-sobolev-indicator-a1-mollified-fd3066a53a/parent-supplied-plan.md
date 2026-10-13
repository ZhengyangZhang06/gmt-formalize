# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.de_giorgi-a1.density_estimates-a1.sobolev_indicator-a1.mollified_integral_tendsto-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-de-giorgi-a1-density-estimates-a1-sobolev-indicator-a1-mollified-fd3066a53a/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.de_giorgi-a1.density_estimates-a1.sobolev_indicator-a1`
- Child key: `mollified_integral_tendsto`
- Declaration: `Submission.deGiorgiSobInd_mollified_integral_tendsto`
- Exact Lean type: `∀ (N : ℕ) (μ : Measure (Rn N)) (ζ : Rn N → ℝ) (ρ : ℕ → Rn N → ℝ) (r : ℕ → ℝ) (δ : ℝ), Continuous ζ → HasCompactSupport ζ → μ (Metric.cthickening δ (tsupport ζ)) < ∞ → (∀ j, Continuous (ρ j)) → (∀ j y, 0 ≤ ρ j y) → (∀ j, ∫ y, ρ j y = 1) → (∀ j, tsupport (ρ j) ⊆ Metric.closedBall (0 : Rn N) (r j)) → (∀ j, r j ≤ δ) → Tendsto r atTop (𝓝 0) → Tendsto (fun j ↦ ∫ z, (∫ y, ζ y * ρ j (y - z)) ∂μ) atTop (𝓝 (∫ z, ζ z ∂μ))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
