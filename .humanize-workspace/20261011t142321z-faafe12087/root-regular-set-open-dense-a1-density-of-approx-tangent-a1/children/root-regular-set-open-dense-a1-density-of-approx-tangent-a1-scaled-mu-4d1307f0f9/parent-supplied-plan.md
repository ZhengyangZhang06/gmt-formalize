# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.regular_set_open_dense-a1.density_of_approx_tangent-a1.scaled_mult_integral_limit-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-regular-set-open-dense-a1-density-of-approx-tangent-a1-scaled-mu-4d1307f0f9/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.regular_set_open_dense-a1.density_of_approx_tangent-a1`
- Child key: `scaled_mult_integral_limit`
- Declaration: `Submission.rsod_tendsto_scaled_mult_integral`
- Exact Lean type: `∀ (n ℓ : ℕ), 1 ≤ n → ∀ (U : Set (Amb n ℓ)), IsOpen U → ∀ (V : RectifiableVarifold n ℓ U) (x : Amb n ℓ) (P : Submodule ℝ (Amb n ℓ)), x ∈ U → Poincare.SimonGMT.Chapter03.HasWeightedApproximateTangentSpaceAt n V.carrier V.mult x P → Tendsto (fun r : ℝ => (r ^ n)⁻¹ * ∫ z in V.carrier ∩ closedBall x r, V.mult z ∂(μHE[n] : Measure (Amb n ℓ))) (𝓝[>] 0) (𝓝 (unitBallVolume n * V.mult x))`

## Sibling prerequisites

- `root.regular_set_open_dense-a1.density_of_approx_tangent-a1.plane_ball_measure-a1`
- `root.regular_set_open_dense-a1.density_of_approx_tangent-a1.blowup_ball_mass_bounds-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
