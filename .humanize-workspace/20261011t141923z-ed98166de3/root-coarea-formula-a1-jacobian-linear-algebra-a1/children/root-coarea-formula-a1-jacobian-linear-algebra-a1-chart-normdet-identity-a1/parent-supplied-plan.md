# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.coarea_formula-a1.jacobian_linear_algebra-a1.chart_normdet_identity-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-coarea-formula-a1-jacobian-linear-algebra-a1-chart-normdet-identity-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.coarea_formula-a1.jacobian_linear_algebra-a1`
- Child key: `chart_normdet_identity`
- Declaration: `Submission.coarea_normDet_adjoint_mul_normDet_chart`
- Exact Lean type: `∀ (m k : ℕ) (T : Type) [NormedAddCommGroup T] [InnerProductSpace ℝ T] [FiniteDimensional ℝ T] (L : T →ₗ[ℝ] Rn m) (Φ : WithLp 2 (Rn m × Rn k) →ₗ[ℝ] T) (Ψ : Rn k →ₗ[ℝ] T), Function.Bijective Φ → (∀ p, L (Φ p) = WithLp.fst p) → (∀ b, Ψ b = Φ (WithLp.toLp 2 (0, b))) → (LinearMap.adjoint L).normDet * Φ.normDet = Ψ.normDet`

## Sibling prerequisites

- `root.coarea_formula-a1.jacobian_linear_algebra-a1.block_triangular_normdet-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
