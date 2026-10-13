# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.tilt_excess_decay-a1.decay_at_origin-a1.scaled_lp_bounds-a1.holder_scaled_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-decay-a1-decay-at-origin-a1-scaled-lp-bounds-a1-hold-3f373fc36c/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.tilt_excess_decay-a1.decay_at_origin-a1.scaled_lp_bounds-a1`
- Child key: `holder_scaled_bound`
- Declaration: `Submission.tdo_slb_lintegral_rpow_le_scaledLpNorm`
- Exact Lean type: `∀ (n ℓ : ℕ) (U : Set (Amb n ℓ)) (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ) (p q : ℝ) (z w : Amb n ℓ) (s t m : ℝ), 0 < q → q ≤ p → 0 < t → 0 ≤ m → closedBall z s ⊆ closedBall w t → V.weight (closedBall z s) ≤ ENNReal.ofReal m → ∫⁻ x in closedBall z s, ‖H x‖ₑ ^ q ∂V.weight ≤ ENNReal.ofReal (m ^ (1 - q / p) * t ^ (q * (n - p) / p)) * V.scaledLpNorm H p w t ^ q`

## Sibling prerequisites

- `root.tilt_excess_decay-a1.decay_at_origin-a1.scaled_lp_bounds-a1.lintegral_holder-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
