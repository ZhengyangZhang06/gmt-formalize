# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_higher_regularity-a1.graph_tangent_planes-a1.graph_approx_tangent-a1.bilip_integral_tendsto-a1.bilip_measure_comparison-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-higher-regularity-a1-graph-tangent-planes-a1-graph-a-ea1269d719/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_higher_regularity-a1.graph_tangent_planes-a1.graph_approx_tangent-a1.bilip_integral_tendsto-a1`
- Child key: `bilip_measure_comparison`
- Declaration: `Submission.dohr_tp_gat_bilip_measure_comparison`
- Exact Lean type: `∀ (n ℓ : ℕ) (A : Set (Amb n ℓ)) (Φ : Amb n ℓ → Amb n ℓ) (δ : ℝ), MeasurableSet A → 0 ≤ δ → δ < 1 → (∀ p ∈ A, ∀ q ∈ A, ‖Φ p - Φ q - (p - q)‖ ≤ δ * ‖p - q‖) → (μHE[n] : Measure (Amb n ℓ)).restrict (Φ '' A) ≤ ENNReal.ofReal (((1 - δ)⁻¹) ^ n) • Measure.map Φ ((μHE[n] : Measure (Amb n ℓ)).restrict A) ∧ Measure.map Φ ((μHE[n] : Measure (Amb n ℓ)).restrict A) ≤ ENNReal.ofReal (((1 - δ)⁻¹) ^ n) • (μHE[n] : Measure (Amb n ℓ)).restrict (Φ '' A)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
