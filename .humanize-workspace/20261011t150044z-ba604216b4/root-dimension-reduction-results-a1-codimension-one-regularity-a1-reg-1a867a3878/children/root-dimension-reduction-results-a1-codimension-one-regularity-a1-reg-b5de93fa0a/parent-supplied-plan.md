# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.local_unit_rep-a1.chart_perimeter-a1.coeff_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-b5de93fa0a/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.local_unit_rep-a1.chart_perimeter-a1`
- Child key: `coeff_bound`
- Declaration: `Submission.codim1_lur_det_covector_norm_le`
- Exact Lean type: `∀ (P n : ℕ) (A : Euclid P →L[ℝ] Euclid (n + 1)) (p : Euclid (n + 1)) (α : Covector (Euclid P) n), ‖A‖ ≤ 1 → ‖p‖ ≤ 1 → (∀ a : Fin n → Euclid P, α a = Matrix.det (Matrix.of fun r c : Fin (n + 1) => (Fin.cons p (fun k : Fin n => A (a k)) : Fin (n + 1) → Euclid (n + 1)) c r)) → covectorEuclideanNorm α ≤ ((n + 1).factorial : ℝ) * Real.sqrt ((P : ℝ) ^ n)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
