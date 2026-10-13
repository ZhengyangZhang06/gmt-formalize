# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.allard_any_radius-a1.graph_rate-a1.lp_ball_bounds-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-any-radius-a1-graph-rate-a1-lp-ball-bounds-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.allard_any_radius-a1.graph_rate-a1`
- Child key: `lp_ball_bounds`
- Declaration: `Submission.any_radius_gr_scaled_lp_ball_bounds`
- Exact Lean type: `∀ (n ℓ : ℕ), 1 ≤ n → ∀ p : ℝ, (n : ℝ) < p → ∀ (U : Set (Amb n ℓ)) (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ) (z : Amb n ℓ) (r ρ : ℝ), 0 < r → r ≤ ρ → closedBall z r ⊆ closedBall 0 ρ → V.scaledLpNorm H p z r ≤ V.scaledLpNorm H p 0 ρ ∧ ∀ δ : ℝ, 0 ≤ δ → V.scaledLpNorm H p 0 ρ ≤ ENNReal.ofReal δ → V.weight (closedBall z r) < ⊤ → ∫ x in closedBall z r, ‖H x‖ ∂V.weight ≤ δ * ρ ^ ((n : ℝ) / p - 1) * (V.weight (closedBall z r)).toReal ^ (1 - 1 / p)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
