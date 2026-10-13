# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_higher_regularity-a1.graph_tangent_planes-a1.graph_approx_tangent-a1.bilip_integral_tendsto-a1.bilip_integral_sandwich-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-higher-regularity-a1-graph-tangent-planes-a1-graph-a-dd02ad2100/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_higher_regularity-a1.graph_tangent_planes-a1.graph_approx_tangent-a1.bilip_integral_tendsto-a1`
- Child key: `bilip_integral_sandwich`
- Declaration: `Submission.dohr_tp_gat_bilip_integral_sandwich`
- Exact Lean type: `∀ (n ℓ : ℕ) (μ₁ μ₂ : Measure (Amb n ℓ)) (φ : Amb n ℓ → ℝ) (κ M : ℝ), IsFiniteMeasure μ₂ → Continuous φ → (∀ w, |φ w| ≤ M) → 1 ≤ κ → μ₁ ≤ ENNReal.ofReal κ • μ₂ → μ₂ ≤ ENNReal.ofReal κ • μ₁ → |∫ w, φ w ∂μ₁ - ∫ w, φ w ∂μ₂| ≤ 2 * ((κ - 1) * κ * (M * (μ₂ univ).toReal))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
