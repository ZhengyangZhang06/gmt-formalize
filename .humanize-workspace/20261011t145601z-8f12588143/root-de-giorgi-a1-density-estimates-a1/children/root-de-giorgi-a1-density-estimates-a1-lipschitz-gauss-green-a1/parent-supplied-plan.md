# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.de_giorgi-a1.density_estimates-a1.lipschitz_gauss_green-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-de-giorgi-a1-density-estimates-a1-lipschitz-gauss-green-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.de_giorgi-a1.density_estimates-a1`
- Child key: `lipschitz_gauss_green`
- Declaration: `Submission.deGiorgiDens_lipschitz_gaussGreen`
- Exact Lean type: `∀ (N : ℕ) (U G : Set (Rn N)) (μ : Measure (Rn N)) (ν : Rn N → Rn N), IsOpen U → NullMeasurableSet G volume → IsGaussGreenPair U G μ ν → ∀ (ζ : Rn N → ℝ) (K : ℝ≥0), LipschitzWith K ζ → HasCompactSupport ζ → tsupport ζ ⊆ U → ∀ w : Rn N, ∫ y in G ∩ U, fderiv ℝ ζ y w = -∫ y, ζ y * inner ℝ w (ν y) ∂μ`

## Sibling prerequisites

- `root.de_giorgi-a1.density_estimates-a1.lipschitz_smooth_approx-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
