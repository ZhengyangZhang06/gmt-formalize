# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.lipschitz_graph_corollary-a1.density_monotonicity-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-lipschitz-graph-corollary-a1-density-monotonicity-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.lipschitz_graph_corollary-a1`
- Child key: `density_monotonicity`
- Declaration: `Submission.lgc_density_monotonicity`
- Exact Lean type: `∀ (n ℓ : ℕ), 1 ≤ n → ∀ p : ℝ, (n : ℝ) < p → ∃ δ₀ C₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 / 8 ∧ 0 ≤ C₀ ∧ ∀ (U : Set (Amb n ℓ)), IsOpen U → ∀ (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ) (δ ρ : ℝ), 0 < δ → δ ≤ δ₀ → V.AllardHypotheses H p δ ρ → (∀ y : Amb n ℓ, ‖y‖ ≤ 3 * δ * ρ → ∀ s : ℝ, 0 < s → s ≤ ρ / 2 → V.weight (closedBall y s) ≤ ENNReal.ofReal (2 * unitBallVolume n * s ^ n)) ∧ (∀ y ∈ V.support, ‖y‖ ≤ 3 * δ * ρ → ∀ s : ℝ, 0 < s → s ≤ ρ / 2 → ENNReal.ofReal (unitBallVolume n * s ^ n / 2) ≤ V.weight (closedBall y s)) ∧ (∀ y : Amb n ℓ, ‖y‖ ≤ 3 * δ * ρ → ∀ s r : ℝ, 0 < s → s ≤ r → r ≤ ρ / 2 → (r ^ n)⁻¹ * (V.weight (closedBall y r)).toReal ≤ Real.exp 2 * ((s ^ n)⁻¹ * (V.weight (closedBall y s)).toReal) + C₀ * δ + Real.exp 2 * ∫ x in closedBall y r \ closedBall y s, ‖(x - y) - V.tangentProj x (x - y)‖ ^ 2 / ‖x - y‖ ^ (n + 2) ∂V.weight)`

## Sibling prerequisites

- `root.lipschitz_graph_corollary-a1.tangent_plane_ae-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
