# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.tangent_structure-a1.first_variation_pieces-a1.image_mass_area_formula-a1.det_tangential_gram-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-tangent-structure-a1-first-variation-pieces-a1-image-mass-area-f-6c3c5ff75b/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.tangent_structure-a1.first_variation_pieces-a1.image_mass_area_formula-a1`
- Child key: `det_tangential_gram`
- Declaration: `Submission.ts_fv_det_tangential_gram_eq`
- Exact Lean type: `∀ (N k : ℕ) (P : Submodule ℝ (EuclideanSpace ℝ (Fin N))) (b : OrthonormalBasis (Fin k) ℝ P) (Λ : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N)), Matrix.det (Matrix.of fun i j : Fin N ↦ inner ℝ (Λ (P.starProjection (EuclideanSpace.single i (1 : ℝ)))) (Λ (P.starProjection (EuclideanSpace.single j (1 : ℝ)))) + inner ℝ (EuclideanSpace.single i (1 : ℝ) - P.starProjection (EuclideanSpace.single i (1 : ℝ))) (EuclideanSpace.single j (1 : ℝ) - P.starProjection (EuclideanSpace.single j (1 : ℝ)))) = Matrix.det (Matrix.of fun a c : Fin k ↦ inner ℝ (Λ (b a)) (Λ (b c)))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
