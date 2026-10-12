# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.tilt_excess_decay-a1.decay_at_origin-a1.one_dim_sup-a1.interval_sup-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-decay-a1-decay-at-origin-a1-one-dim-sup-a1-interval-sup-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.tilt_excess_decay-a1.decay_at_origin-a1.one_dim_sup-a1`
- Child key: `interval_sup`
- Declaration: `Submission.tdo_ods_interval_sup_le`
- Exact Lean type: `∀ (ℓ : ℕ) (W : ℝ → Rn ℓ) (a : ℝ) (K : ℝ≥0), 0 < a → LipschitzOnWith K W (Icc (-a) a) → ∀ t ∈ Icc (-a) a, ‖W t‖ ≤ Real.sqrt ((2 * a)⁻¹ * ∫ s in Ioo (-a) a, ‖W s‖ ^ 2) + Real.sqrt (2 * a * ∫ s in Ioo (-a) a, ‖deriv W s‖ ^ 2)`

## Sibling prerequisites

- `root.tilt_excess_decay-a1.decay_at_origin-a1.one_dim_sup-a1.ftc_bound-a1`
- `root.tilt_excess_decay-a1.decay_at_origin-a1.one_dim_sup-a1.cauchy_schwarz-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
