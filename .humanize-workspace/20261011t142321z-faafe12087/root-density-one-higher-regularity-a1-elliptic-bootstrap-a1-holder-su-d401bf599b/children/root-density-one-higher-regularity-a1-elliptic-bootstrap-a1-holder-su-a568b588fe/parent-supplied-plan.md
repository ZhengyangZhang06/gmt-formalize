# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.holder_succ_iff_fderiv-a1.clm_columns_contdiff-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-higher-regularity-a1-elliptic-bootstrap-a1-holder-su-a568b588fe/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.holder_succ_iff_fderiv-a1`
- Child key: `clm_columns_contdiff`
- Declaration: `Submission.dohr_eb_hsif_contDiffOn_clm_iff_columns`
- Exact Lean type: `∀ (n : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (m : ℕ) (g : Rn n → (Rn n →L[ℝ] E)) (U : Set (Rn n)), ContDiffOn ℝ m g U ↔ ∀ k : Fin n, ContDiffOn ℝ m (fun x => g x (EuclideanSpace.single k (1 : ℝ))) U`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
