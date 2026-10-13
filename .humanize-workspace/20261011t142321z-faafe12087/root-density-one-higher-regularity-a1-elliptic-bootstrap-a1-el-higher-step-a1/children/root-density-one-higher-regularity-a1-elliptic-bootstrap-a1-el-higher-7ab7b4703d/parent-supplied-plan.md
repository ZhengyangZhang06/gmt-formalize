# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.el_higher_step-a1.hessian_apply_smooth-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-higher-regularity-a1-elliptic-bootstrap-a1-el-higher-7ab7b4703d/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.el_higher_step-a1`
- Child key: `hessian_apply_smooth`
- Declaration: `Submission.dohr_eb_ehs_hessian_apply_contDiff`
- Exact Lean type: `∀ n ℓ : ℕ, ∀ Ψ : (Rn n →L[ℝ] Rn ℓ) → ℝ, ContDiff ℝ (⊤ : ℕ∞) Ψ → ∀ P Q : Rn n →L[ℝ] Rn ℓ, ContDiff ℝ (⊤ : ℕ∞) (fun R : Rn n →L[ℝ] Rn ℓ => fderiv ℝ (fderiv ℝ Ψ) R P Q)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
