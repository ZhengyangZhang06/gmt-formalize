# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.linear_higher_regularity-a1.differentiated_system-a1.bilin_leibniz-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-higher-regularity-a1-elliptic-bootstrap-a1-linear-hi-158846722c/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.linear_higher_regularity-a1.differentiated_system-a1`
- Child key: `bilin_leibniz`
- Declaration: `Submission.dohr_eb_lhr_ds_bilin_leibniz`
- Exact Lean type: `∀ (n ℓ : ℕ) (U : Set (Rn n)) (a : Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (w : Rn n → (Rn n →L[ℝ] Rn ℓ)) (e : Rn n), IsOpen U → (∀ P Q : Rn n →L[ℝ] Rn ℓ, ContDiffOn ℝ 1 (fun x => a x P Q) U) → ContDiffOn ℝ 1 w U → ContDiffOn ℝ 1 (fun x => a x (w x)) U ∧ ∀ x ∈ U, ∀ P : Rn n →L[ℝ] Rn ℓ, fderiv ℝ (fun z => a z (w z)) x e P = a x (fderiv ℝ w x e) P + fderiv ℝ (fun z => a z (w x) P) x e`

## Sibling prerequisites

- `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.linear_higher_regularity-a1.differentiated_system-a1.clm_family-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
