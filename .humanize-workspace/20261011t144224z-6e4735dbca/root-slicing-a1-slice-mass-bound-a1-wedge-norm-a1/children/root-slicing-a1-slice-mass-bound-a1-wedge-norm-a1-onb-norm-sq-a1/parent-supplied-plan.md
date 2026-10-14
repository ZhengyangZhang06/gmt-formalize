# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.slicing-a1.slice_mass_bound-a1.wedge_norm-a1.onb_norm_sq-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-mass-bound-a1-wedge-norm-a1-onb-norm-sq-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.slicing-a1.slice_mass_bound-a1.wedge_norm-a1`
- Child key: `onb_norm_sq`
- Declaration: `Submission.slicing_mb_wn_norm_sq_eq_onb_sum`
- Exact Lean type: `∀ (P k : ℕ) (u : OrthonormalBasis (Fin P) ℝ (Eucl P)) (φ : Covector (Eucl P) k), covectorEuclideanNorm φ ^ 2 = ∑ I : Fin k → Fin P, if StrictMono I then (φ (fun i => u (I i))) ^ 2 else 0`

## Sibling prerequisites

- `root.slicing-a1.slice_mass_bound-a1.wedge_norm-a1.count_sq_sum-a1`
- `root.slicing-a1.slice_mass_bound-a1.wedge_norm-a1.parseval_sq_sum-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
