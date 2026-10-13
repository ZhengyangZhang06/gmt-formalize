# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.tilt_excess_decay-a1.decay_at_origin-a1.scaled_lp_bounds-a1.scaling_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-decay-a1-decay-at-origin-a1-scaled-lp-bounds-a1-scal-a33efe07e1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.tilt_excess_decay-a1.decay_at_origin-a1.scaled_lp_bounds-a1`
- Child key: `scaling_bound`
- Declaration: `Submission.tdo_slb_scaledLpNorm_le_of_subset`
- Exact Lean type: `∀ (n ℓ : ℕ) (U : Set (Amb n ℓ)) (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ) (p : ℝ) (z w : Amb n ℓ) (s t : ℝ), 0 < p → 0 < s → s ≤ t → closedBall z s ⊆ closedBall w t → V.scaledLpNorm H p z s ≤ ENNReal.ofReal ((s / t) ^ ((p - n) / p)) * V.scaledLpNorm H p w t`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
