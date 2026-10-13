# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.simons_cone-a1.tangent_fderiv-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-sim-3ee0044a63/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.simons_cone-a1`
- Child key: `tangent_fderiv`
- Declaration: `Submission.codim1_hcp_sc_fderivWithin_tangent_eq`
- Exact Lean type: `∀ (P : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (M : Set (Euclid P)) (f : Euclid P → E) (f' : Euclid P →L[ℝ] E) (x : Euclid P), HasFDerivWithinAt f f' M x → ∀ v ∈ Submodule.span ℝ (tangentSpace M x), fderivWithin ℝ f M x v = f' v`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
