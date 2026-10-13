# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.lipschitz_approximation-a1.good_set_complement-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-lipschitz-approximation-a1-good-set-complement-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.lipschitz_approximation-a1`
- Child key: `good_set_complement`
- Declaration: `Submission.lip_approx_good_set_complement`
- Exact Lean type: `∀ (n ℓ : ℕ), 1 ≤ n → ∀ p : ℝ, (n : ℝ) < p → ∃ δ₀ C₀ : ℝ, 0 < δ₀ ∧ 0 ≤ C₀ ∧ ∀ (U : Set (Amb n ℓ)), IsOpen U → ∀ (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ) (δ ρ : ℝ), 0 < δ → δ ≤ δ₀ → V.AllardHypotheses H p δ ρ → ∀ (T : Submodule ℝ (Amb n ℓ)) (b : ℝ), 0 < b → V.weight (closedBall 0 (3 * (δ * ρ) / 4) \ {y | y ∈ V.support ∧ ∀ s : ℝ, 0 < s → s ≤ δ * ρ / 2 → ∫ x in closedBall y (s / 2), hsNormSq (V.tangentProj x - T.starProjection) ∂V.weight ≤ b * s ^ n}) ≤ ENNReal.ofReal (C₀ / b * ∫ x in closedBall 0 (δ * ρ), hsNormSq (V.tangentProj x - T.starProjection) ∂V.weight)`

## Sibling prerequisites

- `root.lipschitz_approximation-a1.tangent_structure-a1`
- `root.lipschitz_approximation-a1.pinched_density-a1`
- `root.lipschitz_approximation-a1.vitali_bound-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
