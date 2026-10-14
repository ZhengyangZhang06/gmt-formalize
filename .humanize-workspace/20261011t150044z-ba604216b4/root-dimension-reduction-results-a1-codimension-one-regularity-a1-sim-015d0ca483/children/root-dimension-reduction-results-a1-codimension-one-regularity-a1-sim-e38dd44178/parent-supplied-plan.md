# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.area_formula-a1.subspace_gram-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-sim-e38dd44178/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.area_formula-a1`
- Child key: `subspace_gram`
- Declaration: `Submission.codim1_hcp_af_adjoint_det_eq_gram`
- Exact Lean type: `∀ (P k : ℕ) (T : Submodule ℝ (Euclid P)) (B : Euclid P →L[ℝ] Euclid P) (σ : Fin k → Euclid P), Orthonormal ℝ σ → Submodule.span ℝ (Set.range σ) = T → ((B.comp T.subtypeL).adjoint ∘L (B.comp T.subtypeL)).det = Matrix.det (Matrix.of fun i j : Fin k => inner ℝ (B (σ i)) (B (σ j)))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
