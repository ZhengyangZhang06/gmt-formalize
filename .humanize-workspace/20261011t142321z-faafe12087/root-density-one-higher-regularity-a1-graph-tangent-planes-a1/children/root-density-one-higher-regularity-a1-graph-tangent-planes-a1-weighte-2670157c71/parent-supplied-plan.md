# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_higher_regularity-a1.graph_tangent_planes-a1.weighted_tangent_ae-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-higher-regularity-a1-graph-tangent-planes-a1-weighte-2670157c71/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_higher_regularity-a1.graph_tangent_planes-a1`
- Child key: `weighted_tangent_ae`
- Declaration: `Submission.dohr_tp_ae_weighted_tangent_of_growth`
- Exact Lean type: `∀ (n ℓ : ℕ) (M S O : Set (Amb n ℓ)) (θ : Amb n ℓ → ℝ) (C : ℝ), IsOpen O → NullMeasurableSet M (μHE[n] : Measure (Amb n ℓ)) → AEMeasurable θ ((μHE[n] : Measure (Amb n ℓ)).restrict M) → IntegrableOn θ (M ∩ O) (μHE[n] : Measure (Amb n ℓ)) → (μHE[n] : Measure (Amb n ℓ)) ((M ∩ O) \ S) = 0 → (∀ (z : Amb n ℓ) (r : ℝ), 0 < r → (μHE[n] : Measure (Amb n ℓ)) (S ∩ O ∩ closedBall z r) ≤ ENNReal.ofReal (C * r ^ n)) → ∀ᵐ y ∂((μHE[n] : Measure (Amb n ℓ)).restrict M), y ∈ O → ∀ P : Submodule ℝ (Amb n ℓ), Poincare.SimonGMT.Chapter03.HasApproximateTangentSpaceAt n S y P → Poincare.SimonGMT.Chapter03.HasWeightedApproximateTangentSpaceAt n M θ y P`

## Sibling prerequisites

- `root.density_one_higher_regularity-a1.graph_tangent_planes-a1.lebesgue_point_growth-a1`
- `root.density_one_higher_regularity-a1.graph_tangent_planes-a1.weighted_tangent_pointwise-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
