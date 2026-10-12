# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.tilt_excess_decay-a1.decay_at_origin-a1.small_tilt_plane-a1.plane_tilt_comparison-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-decay-a1-decay-at-origin-a1-small-tilt-plane-a1-plan-05a13f71e8/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.tilt_excess_decay-a1.decay_at_origin-a1.small_tilt_plane-a1`
- Child key: `plane_tilt_comparison`
- Declaration: `Submission.tdo_stp_hsNormSq_sub_le_tiltExcess`
- Exact Lean type: `∀ (n ℓ : ℕ) (U : Set (Amb n ℓ)) (V : RectifiableVarifold n ℓ U), AEStronglyMeasurable V.tangentProj V.weight → ∀ (z : Amb n ℓ) (s : ℝ), 0 < s → V.weight (closedBall z s) ≠ ⊤ → ∀ P Q : Submodule ℝ (Amb n ℓ), (V.weight (closedBall z s)).toReal * hsNormSq (P.starProjection - Q.starProjection) ≤ 2 * s ^ n * (V.tiltExcess z s P + V.tiltExcess z s Q)`

## Sibling prerequisites

- `root.lipschitz_graph_corollary-a1.hole_estimate-a1.hs_norm_bounds-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
