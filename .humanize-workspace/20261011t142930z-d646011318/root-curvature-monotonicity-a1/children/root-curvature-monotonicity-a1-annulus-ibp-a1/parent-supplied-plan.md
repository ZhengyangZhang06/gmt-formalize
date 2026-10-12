# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.curvature_monotonicity-a1.annulus_ibp-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-curvature-monotonicity-a1-annulus-ibp-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.curvature_monotonicity-a1`
- Child key: `annulus_ibp`
- Declaration: `Submission.mcm_annulus_integration_by_parts`
- Exact Lean type: `∀ (n ℓ : ℕ) (μ : Measure (Ambient n ℓ)) (ξ : Ambient n ℓ) (w : Ambient n ℓ → ℝ) (a e F F' : ℝ → ℝ) (σ ρ : ℝ), IsFiniteMeasureOnCompacts μ → 0 < σ → σ ≤ ρ → (∀ x, 0 ≤ w x) → IntegrableOn w (closedBall ξ ρ \ closedBall ξ σ) μ → IntegrableOn e (Ioc σ ρ) → (∀ s t : ℝ, σ ≤ s → s ≤ t → t ≤ ρ → a t - a s = ∫ x in closedBall ξ t \ closedBall ξ s, w x ∂μ + ∫ τ in Ioc s t, e τ) → IntegrableOn F' (Ioc σ ρ) → (∀ t ∈ Icc σ ρ, F t = F σ + ∫ τ in Ioc σ t, F' τ) → IntegrableOn (fun x ↦ F ‖x - ξ‖ * w x) (closedBall ξ ρ \ closedBall ξ σ) μ ∧ F ρ * a ρ - F σ * a σ = ∫ x in closedBall ξ ρ \ closedBall ξ σ, F ‖x - ξ‖ * w x ∂μ + ∫ τ in Ioc σ ρ, (F τ * e τ + F' τ * a τ)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
