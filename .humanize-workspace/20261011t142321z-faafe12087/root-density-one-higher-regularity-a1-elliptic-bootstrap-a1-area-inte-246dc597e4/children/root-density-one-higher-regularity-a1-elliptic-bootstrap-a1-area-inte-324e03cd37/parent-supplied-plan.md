# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.area_integrand_legendre-a1.hessian_at_zero-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-higher-regularity-a1-elliptic-bootstrap-a1-area-inte-324e03cd37/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.area_integrand_legendre-a1`
- Child key: `hessian_at_zero`
- Declaration: `Submission.dohr_eb_ail_hessian_zero`
- Exact Lean type: `∀ n ℓ : ℕ, ∀ Q : Rn n →L[ℝ] Rn ℓ, fderiv ℝ (fderiv ℝ (fun P : Rn n →L[ℝ] Rn ℓ => Real.sqrt (Matrix.det ((1 : Matrix (Fin n) (Fin n) ℝ) + Matrix.of fun a b : Fin n => inner ℝ (P (EuclideanSpace.single a (1 : ℝ))) (P (EuclideanSpace.single b (1 : ℝ))))))) 0 Q Q = ∑ a : Fin n, ‖Q (EuclideanSpace.single a (1 : ℝ))‖ ^ 2`

## Sibling prerequisites

- `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.area_integrand_legendre-a1.integrand_smooth-a1`
- `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.area_integrand_legendre-a1.line_second_deriv-a1`
- `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.area_integrand_legendre-a1.sqrt_det_second_deriv-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
