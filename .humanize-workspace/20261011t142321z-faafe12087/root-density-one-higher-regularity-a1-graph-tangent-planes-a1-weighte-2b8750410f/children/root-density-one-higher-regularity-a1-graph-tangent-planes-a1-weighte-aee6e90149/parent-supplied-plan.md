# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_higher_regularity-a1.graph_tangent_planes-a1.weighted_tangent_pointwise-a1.ball_comparison_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-higher-regularity-a1-graph-tangent-planes-a1-weighte-aee6e90149/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_higher_regularity-a1.graph_tangent_planes-a1.weighted_tangent_pointwise-a1`
- Child key: `ball_comparison_bound`
- Declaration: `Submission.dohr_tp_wtlp_ball_comparison_le`
- Exact Lean type: `∀ (n ℓ : ℕ) (M S B : Set (Amb n ℓ)) (θ ψ : Amb n ℓ → ℝ) (c K : ℝ), MeasurableSet B → NullMeasurableSet M (μHE[n] : Measure (Amb n ℓ)) → AEMeasurable θ ((μHE[n] : Measure (Amb n ℓ)).restrict M) → (μHE[n] : Measure (Amb n ℓ)) ((M ∩ B) \ S) = 0 → (μHE[n] : Measure (Amb n ℓ)) (S ∩ B) ≠ ⊤ → Measurable ψ → (∀ w, |ψ w| ≤ K) → (∀ w, w ∉ B → ψ w = 0) → ∫⁻ w in S ∩ B, ‖M.indicator θ w - c‖ₑ ∂(μHE[n] : Measure (Amb n ℓ)) ≠ ⊤ → |∫ w in M, ψ w * θ w ∂(μHE[n] : Measure (Amb n ℓ)) - c * ∫ w in S, ψ w ∂(μHE[n] : Measure (Amb n ℓ))| ≤ K * (∫⁻ w in S ∩ B, ‖M.indicator θ w - c‖ₑ ∂(μHE[n] : Measure (Amb n ℓ))).toReal`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
