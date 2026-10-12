# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.first_rectifiability-a1.tangent_density-a1.density_squeeze-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-first-rectifiability-a1-tangent-density-a1-density-squeeze-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.first_rectifiability-a1.tangent_density-a1`
- Child key: `density_squeeze`
- Declaration: `Submission.frt_td_hasDensity_of_ball_mass_bounds`
- Exact Lean type: `∀ (N n : ℕ) (μ : Measure (Euclidean N)) (x : Euclidean N) (a : ℝ≥0∞), (∀ c : ℝ≥0∞, c < a * unitBallVolume n → ∀ᶠ t in 𝓝[>] (0 : ℝ), c * ENNReal.ofReal t ^ n ≤ μ (closedBall x t)) → (∀ c : ℝ≥0∞, a * unitBallVolume n < c → ∀ᶠ t in 𝓝[>] (0 : ℝ), μ (closedBall x t) ≤ c * ENNReal.ofReal t ^ n) → HasDensity n μ x a`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
