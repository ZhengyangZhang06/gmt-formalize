# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.tilt_excess_decay-a1.decay_at_origin-a1.graph_height_excess-a1.ball_lintegral_ofreal-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-decay-a1-decay-at-origin-a1-graph-height-excess-a1-b-9c6287c6af/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.tilt_excess_decay-a1.decay_at_origin-a1.graph_height_excess-a1`
- Child key: `ball_lintegral_ofreal`
- Declaration: `Submission.tdo_ghe_lintegral_closedBall_ofReal_eq`
- Exact Lean type: `∀ (n : ℕ) (φ : Rn n → ℝ) (r : ℝ), 0 < r → ContinuousOn φ (closedBall 0 r) → (∀ x ∈ closedBall (0 : Rn n) r, 0 ≤ φ x) → ∫⁻ x in closedBall (0 : Rn n) r, ENNReal.ofReal (φ x) = ENNReal.ofReal (∫ x in ball (0 : Rn n) r, φ x)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
