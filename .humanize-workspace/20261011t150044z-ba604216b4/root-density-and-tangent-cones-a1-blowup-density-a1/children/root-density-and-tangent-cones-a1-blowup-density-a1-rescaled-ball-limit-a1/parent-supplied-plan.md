# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_and_tangent_cones-a1.blowup_density-a1.rescaled_ball_limit-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-density-a1-rescaled-ball-limit-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_and_tangent_cones-a1.blowup_density-a1`
- Child key: `rescaled_ball_limit`
- Declaration: `Submission.dtc_rescaled_ball_measure_tendsto`
- Exact Lean type: `∀ (P n : ℕ) (μ : Measure (Euclid P)) (μs : ℕ → Measure (Euclid P)) (x : Euclid P) (θ : ℝ) (lams : ℕ → ℝ), (∀ j, 0 < lams j) → Tendsto lams atTop (𝓝 0) → Tendsto (fun r : ℝ => μ (ball x r) / (unitBallVolume n * ENNReal.ofReal (r ^ n))) (𝓝[>] 0) (𝓝 (ENNReal.ofReal θ)) → (∀ (j : ℕ) (s : Set (Euclid P)), MeasurableSet s → μs j s = ENNReal.ofReal ((lams j)⁻¹ ^ n) * μ (dilation x (lams j) ⁻¹' s)) → ∀ ρ : ℝ, 0 < ρ → Tendsto (fun j => μs j (ball 0 ρ)) atTop (𝓝 (unitBallVolume n * ENNReal.ofReal (ρ ^ n) * ENNReal.ofReal θ))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
