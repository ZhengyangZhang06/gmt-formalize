# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.el_c2alpha-a1.hessian_bounds-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-higher-regularity-a1-elliptic-bootstrap-a1-el-c2alph-11ea4461c4/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.el_c2alpha-a1`
- Child key: `hessian_bounds`
- Declaration: `Submission.dohr_eb_elc2_hessian_bounds`
- Exact Lean type: `∀ (n ℓ : ℕ) (Ψ : (Rn n →L[ℝ] Rn ℓ) → ℝ), ContDiff ℝ 3 Ψ → ∀ ε : ℝ, ∃ MB LB : ℝ, 0 ≤ MB ∧ 0 ≤ LB ∧ (∀ P : Rn n →L[ℝ] Rn ℓ, ‖P‖ ≤ ε → ∀ Q Q' : Rn n →L[ℝ] Rn ℓ, |fderiv ℝ (fderiv ℝ Ψ) P Q Q'| ≤ MB * ‖Q‖ * ‖Q'‖) ∧ ∀ P P' : Rn n →L[ℝ] Rn ℓ, ‖P‖ ≤ ε → ‖P'‖ ≤ ε → ∀ Q Q' : Rn n →L[ℝ] Rn ℓ, |fderiv ℝ (fderiv ℝ Ψ) P Q Q' - fderiv ℝ (fderiv ℝ Ψ) P' Q Q'| ≤ LB * ‖P - P'‖ * ‖Q‖ * ‖Q'‖`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
