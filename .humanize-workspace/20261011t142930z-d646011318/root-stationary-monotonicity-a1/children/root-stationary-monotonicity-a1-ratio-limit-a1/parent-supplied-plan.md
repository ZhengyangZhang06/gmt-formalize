# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.stationary_monotonicity-a1.ratio_limit-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-stationary-monotonicity-a1-ratio-limit-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.stationary_monotonicity-a1`
- Child key: `ratio_limit`
- Declaration: `Submission.stationary_ratio_limit_of_annulus_identity`
- Exact Lean type: `∀ (n ℓ : ℕ) (V : RectifiableVarifold n ℓ) (ξ : Ambient n ℓ) (R : ℝ), (∀ σ ρ : ℝ, 0 < σ → σ ≤ ρ → ρ < R → IntegrableOn (fun x ↦ V.normalRadialSq ξ x / ‖x - ξ‖ ^ n) (closedBall ξ ρ \ closedBall ξ σ) V.weight ∧ V.weight.real (closedBall ξ ρ) / ρ ^ n - V.weight.real (closedBall ξ σ) / σ ^ n = ∫ x in closedBall ξ ρ \ closedBall ξ σ, V.normalRadialSq ξ x / ‖x - ξ‖ ^ n ∂V.weight) → MonotoneOn (fun ρ ↦ V.weight.real (closedBall ξ ρ) / ρ ^ n) (Ioo 0 R) ∧ (∀ ρ : ℝ, 0 < ρ → ρ < R → IntegrableOn (fun x ↦ V.normalRadialSq ξ x / ‖x - ξ‖ ^ n) (closedBall ξ ρ) V.weight ∧ V.weight.real (closedBall ξ ρ) / (omega n * ρ ^ n) - V.density ξ = (omega n)⁻¹ * ∫ x in closedBall ξ ρ, V.normalRadialSq ξ x / ‖x - ξ‖ ^ n ∂V.weight) ∧ (0 < R → V.HasDensityAt ξ (V.density ξ)) ∧ ∀ ρ : ℝ, 0 < ρ → ρ < R → V.density ξ ≤ V.weight.real (closedBall ξ ρ) / (omega n * ρ ^ n)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
