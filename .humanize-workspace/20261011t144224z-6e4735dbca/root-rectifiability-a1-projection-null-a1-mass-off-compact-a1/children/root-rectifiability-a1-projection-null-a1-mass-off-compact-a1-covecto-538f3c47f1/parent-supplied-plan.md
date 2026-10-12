# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.rectifiability-a1.projection_null-a1.mass_off_compact-a1.covector_eval_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-rectifiability-a1-projection-null-a1-mass-off-compact-a1-covecto-538f3c47f1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.rectifiability-a1.projection_null-a1.mass_off_compact-a1`
- Child key: `covector_eval_bound`
- Declaration: `Submission.rpn_moc_abs_covector_apply_le`
- Exact Lean type: `∀ (P n : ℕ) (φ : Covector (Eucl P) n) (v : Fin n → Eucl P), |φ v| ≤ (∑ β : SimonMultiIndex n P, |wedgeCovectors n (fun j => (EuclideanSpace.proj (β j) : Eucl P →L[ℝ] ℝ)) v|) * covectorEuclideanNorm φ`

## Sibling prerequisites

- `root.compactness_mass_bounds-a1.covector_expansion-a1`
- `root.compactness_mass_bounds-a1.repr_bound-a1.coord_bound-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
