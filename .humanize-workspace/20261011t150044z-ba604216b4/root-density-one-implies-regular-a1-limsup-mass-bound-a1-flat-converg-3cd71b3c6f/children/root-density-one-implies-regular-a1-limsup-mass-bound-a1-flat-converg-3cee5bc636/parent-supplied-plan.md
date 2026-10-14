# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.im_pushforward-a1.lipschitz_jacobian_locality-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-flat-converg-3cee5bc636/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.im_pushforward-a1`
- Child key: `lipschitz_jacobian_locality`
- Declaration: `Submission.dor_lmb_fcd_imp_lipschitz_jacobian_locality`
- Exact Lean type: `(∀ (k N N' : ℕ) (F : Euclid N → Euclid N') (G : Euclid k → Euclid N) (Λ : NNReal) (u : Euclid k), LipschitzWith Λ F → DifferentiableAt ℝ G u → Real.sqrt (Matrix.det (Matrix.of fun a b : Fin k => inner ℝ (fderiv ℝ (F ∘ G) u (EuclideanSpace.single a (1 : ℝ))) (fderiv ℝ (F ∘ G) u (EuclideanSpace.single b (1 : ℝ))))) ≤ (Λ : ℝ) ^ k * Real.sqrt (Matrix.det (Matrix.of fun a b : Fin k => inner ℝ (fderiv ℝ G u (EuclideanSpace.single a (1 : ℝ))) (fderiv ℝ G u (EuclideanSpace.single b (1 : ℝ)))))) ∧ ∀ (k N' : ℕ) (H H' : Euclid k → Euclid N') (B : Set (Euclid k)) (L L' : NNReal), LipschitzWith L H → LipschitzWith L' H' → MeasurableSet B → (∀ᵐ u ∂(volume.restrict B), H u = H' u) → ∀ᵐ u ∂(volume.restrict B), fderiv ℝ H u = fderiv ℝ H' u`

## Sibling prerequisites

- `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.local_unit_rep-a1.area_formula-a1.gram_area-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
