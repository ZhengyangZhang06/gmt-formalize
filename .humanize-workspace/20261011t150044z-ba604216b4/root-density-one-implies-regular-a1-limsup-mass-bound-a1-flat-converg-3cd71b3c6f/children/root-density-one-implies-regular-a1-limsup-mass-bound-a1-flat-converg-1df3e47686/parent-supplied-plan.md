# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.im_pushforward-a1.parametric_rep-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-flat-converg-1df3e47686/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.im_pushforward-a1`
- Child key: `parametric_rep`
- Declaration: `Submission.dor_lmb_fcd_imp_parametric_rep`
- Exact Lean type: `∀ (N k : ℕ) (R : IMRep (univ : Set (Euclid N)) k), R.measure univ ≠ ∞ → ∃ (G : ℕ → Euclid k → Euclid N) (B : ℕ → Set (Euclid k)) (w : ℕ → Euclid k → ℝ), (∀ i, ∃ L : NNReal, LipschitzWith L (G i)) ∧ (∀ i, MeasurableSet (B i)) ∧ (∀ i, ∀ u ∈ B i, DifferentiableAt ℝ (G i) u) ∧ (∀ i, Measurable (w i)) ∧ (∀ i u, ∃ z : ℤ, w i u = z) ∧ (∀ i, ∀ u ∈ B i, w i u ≠ 0) ∧ (∀ i, IntegrableOn (w i) (B i)) ∧ ∑' i, ∫⁻ u in B i, ‖w i u‖ₑ * ENNReal.ofReal (Real.sqrt (Matrix.det (Matrix.of fun a b : Fin k => inner ℝ (fderiv ℝ (G i) u (EuclideanSpace.single a (1 : ℝ))) (fderiv ℝ (G i) u (EuclideanSpace.single b (1 : ℝ)))))) ≤ R.measure univ ∧ (∀ γ : Euclid N → Covector (Euclid N) k, Continuous γ → (∃ C : ℝ, ∀ x, ‖γ x‖ ≤ C) → HasSum (fun i => ∫ u in B i, w i u * γ (G i u) (fun a => fderiv ℝ (G i) u (EuclideanSpace.single a (1 : ℝ)))) (R.action γ)) ∧ ∀ p : Euclid N → Prop, (∀ᵐ x ∂(μHE[k].restrict R.carrier), p x) → ∀ i, ∀ᵐ u ∂(volume.restrict (B i)), p (G i u)`

## Sibling prerequisites

- `root.minimizing_implies_stationary-a1.diffeo_pushforward-a1.bilipschitz_pieces-a1`
- `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.local_unit_rep-a1.area_formula-a1.gram_area-a1`
- `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.im_pushforward-a1.piece_orientation_sign-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
