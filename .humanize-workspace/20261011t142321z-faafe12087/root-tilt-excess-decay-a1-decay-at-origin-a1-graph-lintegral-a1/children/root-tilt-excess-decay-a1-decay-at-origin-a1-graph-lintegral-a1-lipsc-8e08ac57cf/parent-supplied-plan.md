# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.tilt_excess_decay-a1.decay_at_origin-a1.graph_lintegral-a1.lipschitz_image_lintegral-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-decay-a1-decay-at-origin-a1-graph-lintegral-a1-lipsc-8e08ac57cf/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.tilt_excess_decay-a1.decay_at_origin-a1.graph_lintegral-a1`
- Child key: `lipschitz_image_lintegral`
- Declaration: `Submission.tdo_gl_lintegral_image_le`
- Exact Lean type: `∀ (n N : ℕ) (F : Rn n → EuclideanSpace ℝ (Fin N)) (D : Set (Rn n)) (K : ℝ≥0), MeasurableSet D → LipschitzOnWith K F D → ∀ g : EuclideanSpace ℝ (Fin N) → ℝ≥0∞, Measurable g → ∫⁻ x in F '' D, g x ∂(μHE[n] : Measure (EuclideanSpace ℝ (Fin N))) ≤ (K : ℝ≥0∞) ^ n * ∫⁻ x' in D, g (F x')`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
