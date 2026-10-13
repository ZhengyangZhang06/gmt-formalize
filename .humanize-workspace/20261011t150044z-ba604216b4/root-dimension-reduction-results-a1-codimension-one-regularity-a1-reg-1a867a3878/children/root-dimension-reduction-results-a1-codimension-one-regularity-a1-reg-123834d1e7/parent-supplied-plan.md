# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.local_unit_rep-a1.chart_perimeter-a1.det_laplace-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-123834d1e7/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.local_unit_rep-a1.chart_perimeter-a1`
- Child key: `det_laplace`
- Declaration: `Submission.codim1_lur_det_laplace_first_column`
- Exact Lean type: `∀ (n : ℕ) (p : Euclid (n + 1)) (j : Fin (n + 1)), Matrix.det (Matrix.of fun r c : Fin (n + 1) => (Fin.cons p (fun k : Fin n => EuclideanSpace.single (j.succAbove k) (1 : ℝ)) : Fin (n + 1) → Euclid (n + 1)) c r) = (-1 : ℝ) ^ (j : ℕ) * p j`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
