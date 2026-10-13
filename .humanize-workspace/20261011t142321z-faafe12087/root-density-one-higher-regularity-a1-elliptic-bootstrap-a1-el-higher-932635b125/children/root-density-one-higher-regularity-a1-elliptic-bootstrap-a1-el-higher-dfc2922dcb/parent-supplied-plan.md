# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.el_higher_step-a1.differentiated_el-a1.chain_symm-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-higher-regularity-a1-elliptic-bootstrap-a1-el-higher-dfc2922dcb/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.el_higher_step-a1.differentiated_el-a1`
- Child key: `chain_symm`
- Declaration: `Submission.dohr_eb_ehs_del_chain_symm`
- Exact Lean type: `∀ n ℓ : ℕ, ∀ (Ψ : (Rn n →L[ℝ] Rn ℓ) → ℝ) (U : Set (Rn n)) (u : Rn n → Rn ℓ), IsOpen U → ContDiff ℝ 2 Ψ → ContDiffOn ℝ 2 u U → ∀ (e y : Rn n), y ∈ U → fderiv ℝ (fun z => fderiv ℝ Ψ (fderiv ℝ u z)) y e = fderiv ℝ (fderiv ℝ Ψ) (fderiv ℝ u y) (fderiv ℝ (fun z => fderiv ℝ u z e) y)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
