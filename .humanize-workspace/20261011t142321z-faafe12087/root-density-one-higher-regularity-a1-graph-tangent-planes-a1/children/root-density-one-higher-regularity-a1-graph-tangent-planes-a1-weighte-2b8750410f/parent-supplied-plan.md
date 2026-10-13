# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_higher_regularity-a1.graph_tangent_planes-a1.weighted_tangent_pointwise-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-higher-regularity-a1-graph-tangent-planes-a1-weighte-2b8750410f/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_higher_regularity-a1.graph_tangent_planes-a1`
- Child key: `weighted_tangent_pointwise`
- Declaration: `Submission.dohr_tp_weighted_tangent_of_lebesgue_point`
- Exact Lean type: `∀ (n ℓ : ℕ) (M S : Set (Amb n ℓ)) (θ : Amb n ℓ → ℝ) (y : Amb n ℓ) (P : Submodule ℝ (Amb n ℓ)) (ε : ℝ), 0 < ε → NullMeasurableSet M (μHE[n] : Measure (Amb n ℓ)) → AEMeasurable θ ((μHE[n] : Measure (Amb n ℓ)).restrict M) → (μHE[n] : Measure (Amb n ℓ)) ((M ∩ ball y ε) \ S) = 0 → (μHE[n] : Measure (Amb n ℓ)) (S ∩ ball y ε) ≠ ⊤ → Poincare.SimonGMT.Chapter03.HasApproximateTangentSpaceAt n S y P → Tendsto (fun r : ℝ => ENNReal.ofReal ((r ^ n)⁻¹) * ∫⁻ w in S ∩ closedBall y r, ‖M.indicator θ w - θ y‖ₑ ∂(μHE[n] : Measure (Amb n ℓ))) (𝓝[>] 0) (𝓝 0) → Poincare.SimonGMT.Chapter03.HasWeightedApproximateTangentSpaceAt n M θ y P`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
