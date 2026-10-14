# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_constant_density_planar-a1.sheet_first_variation-a1.tangent_space_dim-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-46c36a0580/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_constant_density_planar-a1.sheet_first_variation-a1`
- Child key: `tangent_space_dim`
- Declaration: `Submission.idtp_ccd_sfv_span_tangentSpace_finrank`
- Exact Lean type: `∀ (P d : ℕ) (M : Set (Euclid P)) (x : Euclid P), IsEmbeddedSubmanifold 1 d M → x ∈ M → (Submodule.span ℝ (tangentSpace M x) : Set (Euclid P)) = tangentSpace M x ∧ Module.finrank ℝ (Submodule.span ℝ (tangentSpace M x)) = d`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
