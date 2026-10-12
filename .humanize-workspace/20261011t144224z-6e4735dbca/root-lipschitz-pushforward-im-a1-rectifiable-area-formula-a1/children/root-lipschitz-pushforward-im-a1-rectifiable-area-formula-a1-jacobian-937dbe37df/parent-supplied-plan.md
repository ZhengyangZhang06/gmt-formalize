# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.lipschitz_pushforward_im-a1.rectifiable_area_formula-a1.jacobian_identity-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-rectifiable-area-formula-a1-jacobian-937dbe37df/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.lipschitz_pushforward_im-a1.rectifiable_area_formula-a1`
- Child key: `jacobian_identity`
- Declaration: `Submission.lpf_raf_jacobian_identity`
- Exact Lean type: `((∀ (P n : ℕ) (v : Fin n → Eucl P), ‖simpleNVector v‖ ^ 2 = (Matrix.of fun i j => inner ℝ (v i) (v j)).det) ∧ ∀ (P n : ℕ) (B : Matrix (Fin n) (Fin n) ℝ) (τ : Fin n → Eucl P), simpleNVector (fun i => ∑ j, B i j • τ j) = B.det • simpleNVector τ) → ∀ (P Q n : ℕ) (A : Eucl n →L[ℝ] Eucl P) (τ : Fin n → Eucl P) (ξ : NVector (Eucl P) n) (L : Eucl P →L[ℝ] Eucl Q), Orthonormal ℝ τ → (∀ v, A v ∈ Submodule.span ℝ (range τ)) → (ξ = simpleNVector τ ∨ ξ = -simpleNVector τ) → ‖nVectorPushforward n L ξ‖ * Real.sqrt (Matrix.of fun i j => inner ℝ (A (EuclideanSpace.single i 1)) (A (EuclideanSpace.single j 1))).det = Real.sqrt (Matrix.of fun i j => inner ℝ (L (A (EuclideanSpace.single i 1))) (L (A (EuclideanSpace.single j 1)))).det`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
