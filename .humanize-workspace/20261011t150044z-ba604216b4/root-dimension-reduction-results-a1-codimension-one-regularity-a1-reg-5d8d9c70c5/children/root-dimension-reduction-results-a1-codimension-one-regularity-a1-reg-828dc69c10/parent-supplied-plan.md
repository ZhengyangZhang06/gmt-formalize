# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.local_unit_rep-a1.wedge_orientation-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-828dc69c10/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.local_unit_rep-a1`
- Child key: `wedge_orientation`
- Declaration: `Submission.codim1_lur_normalized_wedge_orientation`
- Exact Lean type: `∀ (P n : ℕ) (a : Fin n → Euclid P), LinearIndependent ℝ a → 0 < Matrix.det (Matrix.of fun i j : Fin n => inner ℝ (a i) (a j)) ∧ ∀ ξ : MultiVector P n, (∀ α : Covector (Euclid P) n, ξ α = (Real.sqrt (Matrix.det (Matrix.of fun i j : Fin n => inner ℝ (a i) (a j))))⁻¹ * α a) → IsUnitOrientationOf ξ (Submodule.span ℝ (Set.range a))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
