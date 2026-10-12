# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.curvature_monotonicity-a1.annulus_ibp-a1.annulus_fubini-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-curvature-monotonicity-a1-annulus-ibp-a1-annulus-fubini-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.curvature_monotonicity-a1.annulus_ibp-a1`
- Child key: `annulus_fubini`
- Declaration: `Submission.mcm_annulus_primitive_fubini`
- Exact Lean type: `∀ (n ℓ : ℕ) (μ : Measure (Ambient n ℓ)) (ξ : Ambient n ℓ) (w : Ambient n ℓ → ℝ) (F F' : ℝ → ℝ) (σ ρ : ℝ), IsFiniteMeasureOnCompacts μ → IntegrableOn w (closedBall ξ ρ \ closedBall ξ σ) μ → IntegrableOn F' (Ioc σ ρ) → (∀ t ∈ Icc σ ρ, F t = F σ + ∫ τ in Ioc σ t, F' τ) → IntegrableOn (fun x ↦ w x * (F ‖x - ξ‖ - F σ)) (closedBall ξ ρ \ closedBall ξ σ) μ ∧ IntegrableOn (fun t ↦ F' t * ∫ x in closedBall ξ ρ \ closedBall ξ t, w x ∂μ) (Ioc σ ρ) ∧ ∫ t in Ioc σ ρ, F' t * ∫ x in closedBall ξ ρ \ closedBall ξ t, w x ∂μ = ∫ x in closedBall ξ ρ \ closedBall ξ σ, w x * (F ‖x - ξ‖ - F σ) ∂μ`

## Sibling prerequisites

- `root.curvature_monotonicity-a1.annulus_ibp-a1.primitive_fubini-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
