# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.curvature_monotonicity-a1.exp_integral_ftc-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-curvature-monotonicity-a1-exp-integral-ftc-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.curvature_monotonicity-a1`
- Child key: `exp_integral_ftc`
- Declaration: `Submission.mcm_exp_neg_integral_ftc`
- Exact Lean type: `∀ (g : ℝ → ℝ) (R : ℝ), IntegrableOn g (Ioc 0 R) → IntegrableOn (fun τ ↦ -(g τ * Real.exp (-∫ s in Ioc 0 τ, g s))) (Ioc 0 R) ∧ ∀ σ t : ℝ, 0 ≤ σ → σ ≤ t → t ≤ R → Real.exp (-∫ s in Ioc 0 t, g s) = Real.exp (-∫ s in Ioc 0 σ, g s) + ∫ τ in Ioc σ t, -(g τ * Real.exp (-∫ s in Ioc 0 τ, g s))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
