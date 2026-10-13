# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.linear_higher_regularity-a1.differentiated_system-a1.dir_deriv_symm-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-higher-regularity-a1-elliptic-bootstrap-a1-linear-hi-376ad62370/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.linear_higher_regularity-a1.differentiated_system-a1`
- Child key: `dir_deriv_symm`
- Declaration: `Submission.dohr_eb_lhr_ds_fderiv_dirDeriv_eq`
- Exact Lean type: `∀ (n ℓ : ℕ) (U : Set (Rn n)) (v : Rn n → Rn ℓ) (e : Rn n), IsOpen U → ContDiffOn ℝ 2 v U → ∀ x ∈ U, fderiv ℝ (fun z => fderiv ℝ v z e) x = fderiv ℝ (fderiv ℝ v) x e`

## Sibling prerequisites

- `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.linear_higher_regularity-a1.differentiated_system-a1.diffquot_uniform-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
