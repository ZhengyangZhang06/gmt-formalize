# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.tangent_structure-a1.first_variation_pieces-a1.jacobian_derivative-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-tangent-structure-a1-first-variation-pieces-a1-jacobian-derivative-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.tangent_structure-a1.first_variation_pieces-a1`
- Child key: `jacobian_derivative`
- Declaration: `Submission.ts_fv_tangential_jacobian_hasDerivAt`
- Exact Lean type: `∀ (N : ℕ) (B : ℝ), ∃ C : ℝ, ∀ (P : Submodule ℝ (EuclideanSpace ℝ (Fin N))) (Λ Λ' : ℝ → (EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N))) (J : ℝ → ℝ) (δ : ℝ), 0 < δ → Λ 0 = 1 → (∀ t ∈ Ioo (-δ) δ, HasDerivAt Λ (Λ' t) t ∧ ‖Λ t‖ ≤ B ∧ ‖Λ' t‖ ≤ B ∧ ∀ v, ‖v‖ ≤ B * ‖Λ t v‖) → (∀ t, J t = Real.sqrt (Matrix.det (Matrix.of fun i j : Fin N ↦ inner ℝ (Λ t (P.starProjection (EuclideanSpace.single i (1 : ℝ)))) (Λ t (P.starProjection (EuclideanSpace.single j (1 : ℝ)))) + inner ℝ (EuclideanSpace.single i (1 : ℝ) - P.starProjection (EuclideanSpace.single i (1 : ℝ))) (EuclideanSpace.single j (1 : ℝ) - P.starProjection (EuclideanSpace.single j (1 : ℝ)))))) → (∀ t ∈ Ioo (-δ) δ, 0 ≤ J t ∧ J t ≤ C ∧ ∃ d : ℝ, HasDerivAt J d t ∧ |d| ≤ C) ∧ HasDerivAt J (LinearMap.trace ℝ (EuclideanSpace ℝ (Fin N)) ((Λ' 0).toLinearMap ∘ₗ P.starProjection.toLinearMap)) 0`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
