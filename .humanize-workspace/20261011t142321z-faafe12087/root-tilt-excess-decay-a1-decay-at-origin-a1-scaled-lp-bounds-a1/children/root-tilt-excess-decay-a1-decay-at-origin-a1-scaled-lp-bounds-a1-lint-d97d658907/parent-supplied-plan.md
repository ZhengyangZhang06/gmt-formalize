# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.tilt_excess_decay-a1.decay_at_origin-a1.scaled_lp_bounds-a1.lintegral_holder-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-decay-a1-decay-at-origin-a1-scaled-lp-bounds-a1-lint-d97d658907/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.tilt_excess_decay-a1.decay_at_origin-a1.scaled_lp_bounds-a1`
- Child key: `lintegral_holder`
- Declaration: `Submission.tdo_slb_setLIntegral_rpow_le_holder`
- Exact Lean type: `∀ (X : Type) [MeasurableSpace X] (μ : Measure X) (B : Set X) (g : X → ℝ≥0∞) (p q : ℝ), 0 < q → q ≤ p → ∫⁻ x in B, g x ^ q ∂μ ≤ (∫⁻ x in B, g x ^ p ∂μ) ^ (q / p) * μ B ^ (1 - q / p)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
