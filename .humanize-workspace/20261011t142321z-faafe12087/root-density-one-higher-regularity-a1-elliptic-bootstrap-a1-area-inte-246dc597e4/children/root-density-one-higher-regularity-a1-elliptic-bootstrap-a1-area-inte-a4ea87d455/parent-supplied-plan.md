# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.area_integrand_legendre-a1.hessian_local_unif-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-higher-regularity-a1-elliptic-bootstrap-a1-area-inte-a4ea87d455/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.area_integrand_legendre-a1`
- Child key: `hessian_local_unif`
- Declaration: `Submission.dohr_eb_ail_hessian_local_unif`
- Exact Lean type: `∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (F : E → ℝ), ContDiff ℝ 2 F → ∀ x₀ : E, ∀ δ : ℝ, 0 < δ → ∃ ε : ℝ, 0 < ε ∧ ∀ x : E, ‖x - x₀‖ ≤ ε → ∀ Q Q' : E, |fderiv ℝ (fderiv ℝ F) x Q Q' - fderiv ℝ (fderiv ℝ F) x₀ Q Q'| ≤ δ * (‖Q‖ * ‖Q'‖)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
