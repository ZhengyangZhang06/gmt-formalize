# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.poincare_inequality-a1.ball_average_estimate-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-poincare-inequality-a1-ball-average-estimate-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.poincare_inequality-a1`
- Child key: `ball_average_estimate`
- Declaration: `Submission.bounded_curvature_ball_average_estimate`
- Exact Lean type: `(∀ (n ℓ : ℕ) (V : RectifiableVarifold n ℓ) (U : Set (Ambient n ℓ)) (H : Ambient n ℓ → Ambient n ℓ) (h : Ambient n ℓ → ℝ) (ξ : Ambient n ℓ) (σ ρ : ℝ), 0 < n → IsFiniteMeasureOnCompacts V.weight → (∀ᵐ x ∂V.weight, Module.finrank ℝ (V.tangentSpace x) = n) → AEStronglyMeasurable (fun x ↦ (V.tangentSpace x).starProjection) V.weight → IsOpen U → V.HasMeanCurvatureIn U H → ContDiffOn ℝ 1 h U → tsupport h ∩ closedBall ξ ρ ⊆ U → 0 < σ → σ ≤ ρ → IntegrableOn (fun τ ↦ (∫ x in closedBall ξ τ, inner ℝ (x - ξ) (V.tangentialGradient h x + h x • H x) ∂V.weight) / τ ^ (n + 1)) (Ioc σ ρ) ∧ IntegrableOn (fun x ↦ h x * (V.normalRadialSq ξ x / ‖x - ξ‖ ^ n)) (closedBall ξ ρ \ closedBall ξ σ) V.weight ∧ (∫ x in closedBall ξ ρ, h x ∂V.weight) / ρ ^ n - (∫ x in closedBall ξ σ, h x ∂V.weight) / σ ^ n = ∫ x in closedBall ξ ρ \ closedBall ξ σ, h x * (V.normalRadialSq ξ x / ‖x - ξ‖ ^ n) ∂V.weight + ∫ τ in Ioc σ ρ, (∫ x in closedBall ξ τ, inner ℝ (x - ξ) (V.tangentialGradient h x + h x • H x) ∂V.weight) / τ ^ (n + 1)) → ∀ (n ℓ : ℕ) (V : RectifiableVarifold n ℓ) (U : Set (Ambient n ℓ)) (H : Ambient n ℓ → Ambient n ℓ) (Λ : ℝ) (g : Ambient n ℓ → ℝ) (y : Ambient n ℓ) (r s : ℝ), 0 < n → IsFiniteMeasureOnCompacts V.weight → (∀ᵐ x ∂V.weight, Module.finrank ℝ (V.tangentSpace x) = n) → AEStronglyMeasurable (fun x ↦ (V.tangentSpace x).starProjection) V.weight → IsOpen U → V.HasMeanCurvatureIn U H → 0 ≤ Λ → (∀ᵐ x ∂V.weight, x ∈ U → ‖H x‖ ≤ Λ) → ContDiffOn ℝ 1 g U → (∀ x ∈ U, 0 ≤ g x) → closedBall y r ⊆ U → 0 < s → s ≤ r → IntegrableOn (fun x ↦ ‖V.tangentialGradient g x‖ * ‖x - y‖ ^ (1 - (n : ℝ))) (closedBall y r) V.weight → (∫ x in closedBall y s, g x ∂V.weight) / s ^ n ≤ Real.exp (Λ * (r - s)) * ((∫ x in closedBall y r, g x ∂V.weight) / r ^ n + (n : ℝ)⁻¹ * ∫ x in closedBall y r, ‖V.tangentialGradient g x‖ * ‖x - y‖ ^ (1 - (n : ℝ)) ∂V.weight)`

## Sibling prerequisites

- `root.poincare_inequality-a1.integral_gronwall-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
