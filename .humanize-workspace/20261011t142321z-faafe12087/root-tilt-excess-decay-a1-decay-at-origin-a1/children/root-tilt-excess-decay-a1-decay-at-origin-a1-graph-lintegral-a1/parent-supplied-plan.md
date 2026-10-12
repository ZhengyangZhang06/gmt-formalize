# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.tilt_excess_decay-a1.decay_at_origin-a1.graph_lintegral-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-decay-a1-decay-at-origin-a1-graph-lintegral-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.tilt_excess_decay-a1.decay_at_origin-a1`
- Child key: `graph_lintegral`
- Declaration: `Submission.tdo_graph_lintegral_le`
- Exact Lean type: `∀ (n ℓ : ℕ) (q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ) (f : Rn n → Rn ℓ) (D : Set (Rn n)) (L : ℝ≥0), MeasurableSet D → LipschitzOnWith L f D → ∀ g : Amb n ℓ → ℝ≥0∞, Measurable g → ∫⁻ x in q '' graphOver f D, g x ∂(μHE[n] : Measure (Amb n ℓ)) ≤ ENNReal.ofReal (Real.sqrt (1 + (L : ℝ) ^ 2) ^ n) * ∫⁻ x' in D, g (q (graphPoint x' (f x')))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
