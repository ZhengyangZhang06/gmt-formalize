# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.mean_curvature_monotonicity-a1.approx_tangent_in_tangent_space-a1.blowup_null_image-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-mean-curvature-monotonicity-a1-ap-01ec1f03ac/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.mean_curvature_monotonicity-a1.approx_tangent_in_tangent_space-a1`
- Child key: `blowup_null_image`
- Declaration: `Submission.dsmc_att_blowUpMap_image_null`
- Exact Lean type: `∀ (P n : ℕ) (E : Set (Euclid P)) (x : Euclid P) (lam : ℝ), lam ≠ 0 → μHE[n] E = 0 → μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x lam '' E) = 0`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
