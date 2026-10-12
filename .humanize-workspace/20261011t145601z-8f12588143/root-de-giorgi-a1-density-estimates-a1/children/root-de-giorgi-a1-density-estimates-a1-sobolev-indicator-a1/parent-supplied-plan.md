# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.de_giorgi-a1.density_estimates-a1.sobolev_indicator-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-de-giorgi-a1-density-estimates-a1-sobolev-indicator-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.de_giorgi-a1.density_estimates-a1`
- Child key: `sobolev_indicator`
- Declaration: `Submission.deGiorgiDens_sobolev_indicator`
- Exact Lean type: `∀ (n : ℕ), ∃ c : ℝ, 0 < c ∧ ∀ (U G : Set (Rn (n + 1))) (μ : Measure (Rn (n + 1))) (ν : Rn (n + 1) → Rn (n + 1)), IsOpen U → NullMeasurableSet G volume → IsGaussGreenPair U G μ ν → ∀ (ζ : Rn (n + 1) → ℝ) (K : ℝ≥0), LipschitzWith K ζ → HasCompactSupport ζ → tsupport ζ ⊆ U → (∀ y, 0 ≤ ζ y) → eLpNorm (G.indicator ζ) ((n + 1 : ℝ≥0∞) / n) volume ≤ ENNReal.ofReal (c * (∫ y, ζ y ∂μ + ∫ y in G, ‖fderiv ℝ ζ y‖))`

## Sibling prerequisites

- `root.de_giorgi-a1.density_estimates-a1.lipschitz_sobolev-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
