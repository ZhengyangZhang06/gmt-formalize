# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.integral_compactness-a1.integral_density-a1.tangent_point_density-a1.ball_mass_lower-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-integral-compactness-a1-integral-density-a1-tangent-point-densit-19a7473d3a/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.integral_compactness-a1.integral_density-a1.tangent_point_density-a1`
- Child key: `ball_mass_lower`
- Declaration: `Submission.intcpt_id_tpd_ball_mass_lower`
- Exact Lean type: `∀ (N n : ℕ) (M : Set (Euclidean N)) (θ : Euclidean N → ℝ) (x : Euclidean N) (P : Submodule ℝ (Euclidean N)) (r₀ : ℝ), NullMeasurableSet M (μHE[n] : Measure (Euclidean N)) → (∀ y ∈ M, 0 ≤ θ y) → 0 < r₀ → IntegrableOn θ (M ∩ closedBall x r₀) μHE[n] → Chapter03.HasWeightedApproximateTangentSpaceAt n M θ x P → ∀ c : ℝ≥0∞, c < ENNReal.ofReal (θ x) * unitBallVolume n → ∀ᶠ t in 𝓝[>] (0 : ℝ), c * ENNReal.ofReal t ^ n ≤ (((μHE[n] : Measure (Euclidean N)).restrict M).withDensity fun y ↦ ENNReal.ofReal (θ y)) (closedBall x t)`

## Sibling prerequisites

- `root.integral_compactness-a1.integral_density-a1.tangent_point_density-a1.ball_sandwich-a1`
- `root.integral_compactness-a1.integral_density-a1.tangent_point_density-a1.plane_cutoff-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
