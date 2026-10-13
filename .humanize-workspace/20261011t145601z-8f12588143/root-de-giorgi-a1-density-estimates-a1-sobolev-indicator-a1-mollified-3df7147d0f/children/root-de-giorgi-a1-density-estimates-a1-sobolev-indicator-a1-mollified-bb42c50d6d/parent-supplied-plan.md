# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.de_giorgi-a1.density_estimates-a1.sobolev_indicator-a1.mollified_fderiv_le-a1.kernel_gauss_green-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-de-giorgi-a1-density-estimates-a1-sobolev-indicator-a1-mollified-bb42c50d6d/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.de_giorgi-a1.density_estimates-a1.sobolev_indicator-a1.mollified_fderiv_le-a1`
- Child key: `kernel_gauss_green`
- Declaration: `Submission.deGiorgiSobIndMFL_setIntegral_fderiv_kernel_eq`
- Exact Lean type: `∀ (N : ℕ) (U G : Set (Rn N)) (μ : Measure (Rn N)) (ν : Rn N → Rn N), IsOpen U → IsGaussGreenPair U G μ ν → ∀ (ρ : Rn N → ℝ) (r : ℝ) (y w : Rn N), ContDiff ℝ 1 ρ → HasCompactSupport ρ → tsupport ρ ⊆ Metric.closedBall (0 : Rn N) r → Metric.closedBall y r ⊆ U → ∫ z in G, fderiv ℝ ρ (y - z) w = ∫ z, ρ (y - z) * inner ℝ w (ν z) ∂μ`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
