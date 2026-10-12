# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_and_tangent_cones-a1.blowup_density-a1.ball_measure_convergence-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-density-a1-ball-measure-convergence-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_and_tangent_cones-a1.blowup_density-a1`
- Child key: `ball_measure_convergence`
- Declaration: `Submission.dtc_tendsto_measure_ball_of_vague`
- Exact Lean type: `∀ (P : ℕ) (μs : ℕ → Measure (Euclid P)) (μ : Measure (Euclid P)) (ρ : ℝ), 0 < ρ → (∀ r : ℝ, 0 < r → μ (ball 0 r) ≠ ∞) → (∀ r : ℝ, 0 < r → ∀ᶠ j in atTop, μs j (ball 0 r) ≠ ∞) → (∀ f : Euclid P → ℝ, Continuous f → HasCompactSupport f → Tendsto (fun j => ∫ y, f y ∂(μs j)) atTop (𝓝 (∫ y, f y ∂μ))) → μ (sphere 0 ρ) = 0 → Tendsto (fun j => μs j (ball 0 ρ)) atTop (𝓝 (μ (ball 0 ρ)))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
