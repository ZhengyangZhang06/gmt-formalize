# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.de_giorgi-a1.density_estimates-a1.sobolev_indicator-a1.mollified_fderiv_le-a1.pointwise_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-de-giorgi-a1-density-estimates-a1-sobolev-indicator-a1-mollified-a53949da46/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.de_giorgi-a1.density_estimates-a1.sobolev_indicator-a1.mollified_fderiv_le-a1`
- Child key: `pointwise_bound`
- Declaration: `Submission.deGiorgiSobIndMFL_norm_fderiv_le`
- Exact Lean type: `∀ (N : ℕ) (U G : Set (Rn N)) (μ : Measure (Rn N)) (ν : Rn N → Rn N), IsOpen U → NullMeasurableSet G volume → IsGaussGreenPair U G μ ν → ∀ (ρ : Rn N → ℝ) (r : ℝ) (y : Rn N), ContDiff ℝ 1 ρ → HasCompactSupport ρ → (∀ x, 0 ≤ ρ x) → tsupport ρ ⊆ Metric.closedBall (0 : Rn N) r → Metric.closedBall y r ⊆ U → ‖fderiv ℝ (fun x ↦ ∫ z in G, ρ (x - z)) y‖ ≤ ∫ z, ρ (y - z) ∂μ`

## Sibling prerequisites

- `root.de_giorgi-a1.density_estimates-a1.sobolev_indicator-a1.mollified_fderiv_le-a1.fderiv_setintegral-a1`
- `root.de_giorgi-a1.density_estimates-a1.sobolev_indicator-a1.mollified_fderiv_le-a1.kernel_gauss_green-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
