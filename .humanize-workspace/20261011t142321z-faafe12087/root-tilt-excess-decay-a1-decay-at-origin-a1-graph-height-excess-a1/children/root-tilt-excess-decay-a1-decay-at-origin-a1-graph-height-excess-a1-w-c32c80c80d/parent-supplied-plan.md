# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.tilt_excess_decay-a1.decay_at_origin-a1.graph_height_excess-a1.weight_density_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-decay-a1-decay-at-origin-a1-graph-height-excess-a1-w-c32c80c80d/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.tilt_excess_decay-a1.decay_at_origin-a1.graph_height_excess-a1`
- Child key: `weight_density_bound`
- Declaration: `Submission.tdo_ghe_setLIntegral_weight_le_mul`
- Exact Lean type: `∀ (n ℓ : ℕ) (U : Set (Amb n ℓ)) (V : RectifiableVarifold n ℓ U) (E : Set (Amb n ℓ)) (C : ℝ) (g : Amb n ℓ → ℝ≥0∞), MeasurableSet E → Measurable g → (∀ᵐ x ∂V.weight, x ∈ E → V.mult x ≤ C) → ∫⁻ x in E, g x ∂V.weight ≤ ENNReal.ofReal C * ∫⁻ x in E, g x ∂(μHE[n] : Measure (Amb n ℓ))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
