# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.coarea_formula-a1.jacobian_linear_algebra-a1.block_triangular_normdet-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-coarea-formula-a1-jacobian-linear-algebra-a1-block-triangular-normdet-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.coarea_formula-a1.jacobian_linear_algebra-a1`
- Child key: `block_triangular_normdet`
- Declaration: `Submission.coarea_normDet_block_triangular`
- Exact Lean type: `∀ (E₁ E₂ F₁ F₂ : Type) [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [FiniteDimensional ℝ E₁] [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [FiniteDimensional ℝ E₂] [NormedAddCommGroup F₁] [InnerProductSpace ℝ F₁] [FiniteDimensional ℝ F₁] [NormedAddCommGroup F₂] [InnerProductSpace ℝ F₂] [FiniteDimensional ℝ F₂] (G : WithLp 2 (E₁ × E₂) →ₗ[ℝ] WithLp 2 (F₁ × F₂)) (G₁₁ : E₁ →ₗ[ℝ] F₁) (G₂₂ : E₂ →ₗ[ℝ] F₂), Module.finrank ℝ E₁ = Module.finrank ℝ F₁ → Module.finrank ℝ E₂ = Module.finrank ℝ F₂ → (∀ b : E₂, WithLp.fst (G (WithLp.toLp 2 (0, b))) = 0) → (∀ a : E₁, G₁₁ a = WithLp.fst (G (WithLp.toLp 2 (a, 0)))) → (∀ b : E₂, G₂₂ b = WithLp.snd (G (WithLp.toLp 2 (0, b)))) → G.normDet = G₁₁.normDet * G₂₂.normDet`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
