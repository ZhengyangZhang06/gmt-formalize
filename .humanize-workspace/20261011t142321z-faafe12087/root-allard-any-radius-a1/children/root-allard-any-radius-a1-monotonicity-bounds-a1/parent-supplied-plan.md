# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.allard_any_radius-a1.monotonicity_bounds-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-any-radius-a1-monotonicity-bounds-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.allard_any_radius-a1`
- Child key: `monotonicity_bounds`
- Declaration: `Submission.any_radius_monotonicity_bounds`
- Exact Lean type: `∀ (n ℓ : ℕ), 1 ≤ n → ∀ p : ℝ, (n : ℝ) < p → ∀ (U : Set (Amb n ℓ)), IsOpen U → ∀ (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ) (δ ρ : ℝ), 0 < δ → δ ≤ (p - n) / (4 * p) → V.AllardHypotheses H p δ ρ → (∀ (y : Amb n ℓ) (R s r : ℝ), 0 < s → s ≤ r → r < R → closedBall y R ⊆ closedBall 0 ρ → (V.weight (closedBall y s)).toReal / s ^ n ≤ Real.exp (2 * (4 * p * δ / (p - n))) * ((V.weight (closedBall y r)).toReal / r ^ n) + 2 * Real.exp (4 * p * δ / (p - n)) * (4 * p * δ / (p - n))) ∧ (∀ y ∈ V.support, ∀ R s : ℝ, 0 < s → s < R → closedBall y R ⊆ closedBall 0 ρ → Real.exp (-(4 * p * δ / (p - n))) * (unitBallVolume n - 4 * p * δ / (p - n)) * s ^ n ≤ (V.weight (closedBall y s)).toReal) ∧ ∫⁻ x in ball (0 : Amb n ℓ) ρ, ENNReal.ofReal (‖x - V.tangentProj x x‖ ^ 2 / ‖x‖ ^ (n + 2)) ∂V.weight ≤ ENNReal.ofReal (Real.exp (4 * p * δ / (p - n)) * (Real.exp (4 * p * δ / (p - n)) * (1 + δ) * unitBallVolume n + 4 * p * δ / (p - n) - unitBallVolume n))`

## Sibling prerequisites

- `root.allard_any_radius-a1.tangent_ae-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
