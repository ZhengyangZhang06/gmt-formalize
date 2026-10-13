# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.allard_any_radius-a1.pinching-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-any-radius-a1-pinching-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.allard_any_radius-a1`
- Child key: `pinching`
- Declaration: `Submission.any_radius_pinching`
- Exact Lean type: `ConicalApproximationTheorem → ∀ (n ℓ : ℕ), 1 ≤ n → ∀ p : ℝ, (n : ℝ) < p → ∀ γ ε : ℝ, 0 < γ → γ < 1 → 0 < ε → ε ≤ 1 / 4 → ∃ δP cs : ℝ, 0 < δP ∧ 0 < cs ∧ cs ≤ (1 - γ) / 16 ∧ ∀ (U : Set (Amb n ℓ)), IsOpen U → ∀ (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ) (δ ρ : ℝ), 0 < δ → δ ≤ δP → V.AllardHypotheses H p δ ρ → ∀ y ∈ V.support ∩ closedBall 0 ((1 + γ) / 2 * ρ), V.weight (closedBall y (cs * ρ)) ≤ ENNReal.ofReal ((1 + ε) * (unitBallVolume n * (cs * ρ) ^ n))`

## Sibling prerequisites

- `root.allard_any_radius-a1.rescaled_varifold-a1`
- `root.allard_any_radius-a1.monotonicity_bounds-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
