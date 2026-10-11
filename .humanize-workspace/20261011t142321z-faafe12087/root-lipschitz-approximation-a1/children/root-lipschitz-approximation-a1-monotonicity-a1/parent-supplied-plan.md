# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.lipschitz_approximation-a1.monotonicity-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-lipschitz-approximation-a1-monotonicity-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.lipschitz_approximation-a1`
- Child key: `monotonicity`
- Declaration: `Submission.lip_approx_monotonicity`
- Exact Lean type: `∀ (n ℓ : ℕ), 1 ≤ n → ∀ p : ℝ, (n : ℝ) < p → ∀ (U : Set (Amb n ℓ)), IsOpen U → ∀ (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ) (δ ρ Λ : ℝ), 0 < δ → V.AllardHypotheses H p δ ρ → 4 * p * δ / (p - n) ≤ Λ → Λ ≤ 1 → ∀ (y : Amb n ℓ) (R : ℝ), 0 < R → closedBall y R ⊆ closedBall 0 ρ → ∀ s r : ℝ, 0 < s → s ≤ r → r < R → V.weight.real (closedBall y s) / s ^ n ≤ Real.exp (2 * Λ) * (V.weight.real (closedBall y r) / r ^ n) + 2 * Real.exp Λ * Λ ∧ V.weight.real (closedBall y r) / r ^ n ≤ Real.exp (2 * Λ) * (V.weight.real (closedBall y s) / s ^ n) + 2 * Real.exp Λ * Λ + Real.exp (2 * Λ) * ∫ x in closedBall y r \ closedBall y s, ‖(x - y) - V.tangentProj x (x - y)‖ ^ 2 / ‖x - y‖ ^ (n + 2) ∂V.weight ∧ (y ∈ V.support → Real.exp (-Λ) * (unitBallVolume n - Λ) ≤ V.weight.real (closedBall y s) / s ^ n)`

## Sibling prerequisites

- `root.lipschitz_approximation-a1.tangent_structure-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
