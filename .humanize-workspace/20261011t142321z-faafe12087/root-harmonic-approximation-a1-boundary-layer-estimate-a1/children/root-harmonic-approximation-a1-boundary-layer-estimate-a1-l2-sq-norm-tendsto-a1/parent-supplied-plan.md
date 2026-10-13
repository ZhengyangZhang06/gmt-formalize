# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.harmonic_approximation-a1.boundary_layer_estimate-a1.l2_sq_norm_tendsto-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-harmonic-approximation-a1-boundary-layer-estimate-a1-l2-sq-norm-tendsto-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.harmonic_approximation-a1.boundary_layer_estimate-a1`
- Child key: `l2_sq_norm_tendsto`
- Declaration: `Submission.ble_lintegral_sq_tendsto_of_l2_tendsto`
- Exact Lean type: `∀ {α : Type} [MeasurableSpace α] {E : Type} [NormedAddCommGroup E] (μ : Measure α) (f : α → E) (φ : ℕ → α → E), MemLp f 2 μ → (∀ j, AEStronglyMeasurable (φ j) μ) → Tendsto (fun j => ∫⁻ x, ‖φ j x - f x‖ₑ ^ 2 ∂μ) atTop (𝓝 0) → Tendsto (fun j => ∫⁻ x, ‖φ j x‖ₑ ^ 2 ∂μ) atTop (𝓝 (∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
