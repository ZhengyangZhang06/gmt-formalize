# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.tilt_excess_decay-a1.decay_at_origin-a1.small_tilt_plane-a1.origin_affine_plane-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-decay-a1-decay-at-origin-a1-small-tilt-plane-a1-orig-99c275edea/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.tilt_excess_decay-a1.decay_at_origin-a1.small_tilt_plane-a1`
- Child key: `origin_affine_plane`
- Declaration: `Submission.tdo_stp_origin_affine_plane`
- Exact Lean type: `AffineApproximationLemma → ∀ n ℓ : ℕ, 1 ≤ n → ∀ p : ℝ, (n : ℝ) < p → ∃ C : ℝ, 0 < C ∧ ∀ (U : Set (Amb n ℓ)), IsOpen U → ∀ (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ) (δ ρ : ℝ), 0 < δ → δ ≤ 1 / 4 → V.AllardHypotheses H p δ ρ → V.scaledLpNorm H p 0 (2 * (δ * ρ)) ≤ ENNReal.ofReal δ → ∃ T : Submodule ℝ (Amb n ℓ), Module.finrank ℝ T = n ∧ V.tiltExcess 0 (δ * ρ) T ≤ C * (δ ^ (1 / (2 * (n : ℝ) + 2))) ^ 2 ∧ ∀ x ∈ V.support ∩ closedBall 0 (2 * (δ * ρ)), infDist x (T : Set (Amb n ℓ)) ≤ C * δ ^ (1 / (2 * (n : ℝ) + 2)) * (δ * ρ)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
