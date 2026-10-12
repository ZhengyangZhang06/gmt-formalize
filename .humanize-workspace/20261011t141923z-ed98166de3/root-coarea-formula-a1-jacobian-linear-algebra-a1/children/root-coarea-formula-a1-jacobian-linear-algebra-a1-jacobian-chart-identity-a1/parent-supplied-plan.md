# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.coarea_formula-a1.jacobian_linear_algebra-a1.jacobian_chart_identity-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-coarea-formula-a1-jacobian-linear-algebra-a1-jacobian-chart-identity-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.coarea_formula-a1.jacobian_linear_algebra-a1`
- Child key: `jacobian_chart_identity`
- Declaration: `Submission.coareaJacobian_mul_normDet_chart`
- Exact Lean type: `∀ (N m k : ℕ) (M : Set (Rn N)) (f : Rn N → Rn m) (x : Rn N) (A : WithLp 2 (Rn m × Rn k) →L[ℝ] Rn N) (B : Rn k →L[ℝ] Rn N), Function.Injective A → tangentSpace M x = LinearMap.range A.toLinearMap → (∀ p, fderiv ℝ f x (A p) = WithLp.fst p) → (∀ b, B b = A (WithLp.toLp 2 (0, b))) → coareaJacobian M f x * A.toLinearMap.normDet = B.toLinearMap.normDet`

## Sibling prerequisites

- `root.coarea_formula-a1.jacobian_linear_algebra-a1.jacobian_normdet_bridge-a1`
- `root.coarea_formula-a1.jacobian_linear_algebra-a1.chart_normdet_identity-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
