# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.allard_any_radius-a1.graph_rate-a1.height_transfer-a1.ae_transfer-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-any-radius-a1-graph-rate-a1-height-transfer-a1-ae-transfer-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.allard_any_radius-a1.graph_rate-a1.height_transfer-a1`
- Child key: `ae_transfer`
- Declaration: `Submission.any_radius_gr_ht_ae_transfer`
- Exact Lean type: `∀ (n ℓ : ℕ) (ν : Measure (Rn n)) (μ : Measure (Amb n ℓ)) (F : Rn n → Amb n ℓ), AEMeasurable F ν → (∀ g : Amb n ℓ → ℝ≥0∞, Measurable g → ∫⁻ x, g (F x) ∂ν ≤ ∫⁻ y, g y ∂μ) → ∀ g : Amb n ℓ → ℝ≥0∞, AEMeasurable g μ → ∫⁻ x, g (F x) ∂ν ≤ ∫⁻ y, g y ∂μ`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
