# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.tilt_excess_decay-a1.decay_at_origin-a1.one_dim_sup-a1.ftc_bound-a1.interval_dominated_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-decay-a1-decay-at-origin-a1-one-dim-sup-a1-ftc-bound-f7d6f53a47/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.tilt_excess_decay-a1.decay_at_origin-a1.one_dim_sup-a1.ftc_bound-a1`
- Child key: `interval_dominated_bound`
- Declaration: `Submission.tdo_ods_intervalIntegral_le_of_ae_abs_le`
- Exact Lean type: `∀ (g h : ℝ → ℝ) (a s t : ℝ), IntegrableOn h (Ioo (-a) a) → s ∈ Icc (-a) a → t ∈ Icc (-a) a → IntervalIntegrable g volume s t → (∀ᵐ r ∂(volume : Measure ℝ), r ∈ Ioo (-a) a → |g r| ≤ h r) → ∫ r in s..t, g r ≤ ∫ r in Ioo (-a) a, h r`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
