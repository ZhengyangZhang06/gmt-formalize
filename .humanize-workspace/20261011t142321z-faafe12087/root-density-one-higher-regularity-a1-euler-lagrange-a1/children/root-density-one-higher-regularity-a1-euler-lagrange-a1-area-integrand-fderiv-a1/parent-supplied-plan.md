# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_higher_regularity-a1.euler_lagrange-a1.area_integrand_fderiv-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-higher-regularity-a1-euler-lagrange-a1-area-integrand-fderiv-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_higher_regularity-a1.euler_lagrange-a1`
- Child key: `area_integrand_fderiv`
- Declaration: `Submission.dohr_vel_area_integrand_fderiv`
- Exact Lean type: `∀ n ℓ : ℕ, ∀ P : Rn n →L[ℝ] Rn ℓ, DifferentiableAt ℝ (fun P' : Rn n →L[ℝ] Rn ℓ => Real.sqrt (Matrix.det ((1 : Matrix (Fin n) (Fin n) ℝ) + Matrix.of fun a b : Fin n => inner ℝ (P' (EuclideanSpace.single a (1 : ℝ))) (P' (EuclideanSpace.single b (1 : ℝ)))))) P ∧ ∀ Ψ : Rn n →L[ℝ] Rn ℓ, fderiv ℝ (fun P' : Rn n →L[ℝ] Rn ℓ => Real.sqrt (Matrix.det ((1 : Matrix (Fin n) (Fin n) ℝ) + Matrix.of fun a b : Fin n => inner ℝ (P' (EuclideanSpace.single a (1 : ℝ))) (P' (EuclideanSpace.single b (1 : ℝ)))))) P Ψ = Real.sqrt (Matrix.det ((1 : Matrix (Fin n) (Fin n) ℝ) + Matrix.of fun a b : Fin n => inner ℝ (P (EuclideanSpace.single a (1 : ℝ))) (P (EuclideanSpace.single b (1 : ℝ))))) * ∑ a : Fin n, ∑ c : Fin n, ((1 : Matrix (Fin n) (Fin n) ℝ) + Matrix.of fun a b : Fin n => inner ℝ (P (EuclideanSpace.single a (1 : ℝ))) (P (EuclideanSpace.single b (1 : ℝ))))⁻¹ a c * inner ℝ (P (EuclideanSpace.single c (1 : ℝ))) (Ψ (EuclideanSpace.single a (1 : ℝ)))`

## Sibling prerequisites

- `root.density_one_higher_regularity-a1.euler_lagrange-a1.linear_graph_area-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
