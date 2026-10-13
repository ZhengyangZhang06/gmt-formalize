# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.lipschitz_approximation-a1.good_set_flat-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-lipschitz-approximation-a1-good-set-flat-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.lipschitz_approximation-a1`
- Child key: `good_set_flat`
- Declaration: `Submission.lip_approx_good_set_flat`
- Exact Lean type: `AffineApproximationLemma → ∀ (n ℓ : ℕ), 1 ≤ n → ∀ p : ℝ, (n : ℝ) < p → ∃ C₀ δ₀ : ℝ, 0 < C₀ ∧ 0 < δ₀ ∧ ∀ β L : ℝ, 0 < β → 0 < L → L ≤ 1 → ∀ (U : Set (Amb n ℓ)), IsOpen U → ∀ (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ) (δ ρ : ℝ), 0 < δ → δ ≤ δ₀ → δ ≤ (β * L) ^ (2 * n + 2) → V.AllardHypotheses H p δ ρ → ∀ q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ, ∫ x in closedBall 0 (δ * ρ), hsNormSq (V.tangentProj x - (rotatedPlane q).starProjection) ∂V.weight ≤ β ^ 2 * L ^ 2 * (δ * ρ) ^ n → (∀ x ∈ V.support ∩ closedBall 0 (2 * (δ * ρ)), infDist x (rotatedPlane q : Set (Amb n ℓ)) ≤ C₀ * β * L * (δ * ρ)) ∧ ∀ y₁ ∈ V.support ∩ closedBall 0 (3 * (δ * ρ) / 4), ∀ y₂ ∈ V.support ∩ closedBall 0 (3 * (δ * ρ) / 4), (∀ s : ℝ, 0 < s → s ≤ δ * ρ / 2 → ∫ x in closedBall y₁ (s / 2), hsNormSq (V.tangentProj x - (rotatedPlane q).starProjection) ∂V.weight ≤ β ^ 2 * L ^ 2 * s ^ n) → ‖(y₂ - y₁) - (rotatedPlane q).starProjection (y₂ - y₁)‖ ≤ C₀ * β * L * ‖y₂ - y₁‖`

## Sibling prerequisites

- `root.lipschitz_approximation-a1.tangent_structure-a1`
- `root.lipschitz_approximation-a1.pinched_density-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
