# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.im_pushforward-a1.piece_current-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-flat-converg-e667478584/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.im_pushforward-a1`
- Child key: `piece_current`
- Declaration: `Submission.dor_lmb_fcd_imp_piece_current`
- Exact Lean type: `((∀ (P n : ℕ) (U M M' : Set (Euclid P)), IsOpen U → MeasurableSet M → MeasurableSet M' → M ⊆ M' → M' ⊆ U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (M' ∩ K) ≠ ∞) → ∀ᵐ x ∂(μHE[n].restrict M), ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n M x Q ↔ HasApproximateTangentSpaceAt n M' x Q) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (E : Set (Euclid P)), IsOpen U → MeasurableSet E → ∃ (A : GeometricCurrentOn U n) (R' : IMRep U n), R'.Represents A ∧ R'.carrier = R.carrier ∩ E ∧ R'.mult = R.mult ∧ R'.orient = R.orient) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (A B : GeometricCurrentOn U n), IsOpen U → IsIntegerMultiplicity A → IsIntegerMultiplicity B → IsIntegerMultiplicity (A - B)) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n), ∀ᵐ x ∂(μHE[n].restrict R.carrier), ∀ α : Covector (Euclid P) n, |R.orient x α| ≤ covectorEuclideanNorm α)) → ∀ (k N' : ℕ) (H : Euclid k → Euclid N') (A : Set (Euclid k)) (L : NNReal) (κ : ℝ) (g : Euclid k → ℝ), LipschitzWith L H → MeasurableSet A → 0 < κ → (∀ a ∈ A, ∀ a' ∈ A, κ * ‖a - a'‖ ≤ ‖H a - H a'‖) → (∀ a ∈ A, DifferentiableAt ℝ H a ∧ Injective (fderiv ℝ H a)) → Measurable g → (∀ u, ∃ z : ℤ, g u = z) → (∀ u ∈ A, g u ≠ 0) → ∫⁻ u in A, ‖g u‖ₑ * ENNReal.ofReal (Real.sqrt (Matrix.det (Matrix.of fun a b : Fin k => inner ℝ (fderiv ℝ H u (EuclideanSpace.single a (1 : ℝ))) (fderiv ℝ H u (EuclideanSpace.single b (1 : ℝ)))))) ≠ ∞ → ∃ Φ : GeometricCurrentOn (univ : Set (Euclid N')) k, IsIntegerMultiplicity Φ ∧ Φ.mass ≤ ∫⁻ u in A, ‖g u‖ₑ * ENNReal.ofReal (Real.sqrt (Matrix.det (Matrix.of fun a b : Fin k => inner ℝ (fderiv ℝ H u (EuclideanSpace.single a (1 : ℝ))) (fderiv ℝ H u (EuclideanSpace.single b (1 : ℝ)))))) ∧ ∀ ω : TestFormOn (univ : Set (Euclid N')) k, Φ ω = ∫ u in A, g u * (ω : DifferentialForm (Euclid N') k) (H u) (fun a => fderiv ℝ H u (EuclideanSpace.single a (1 : ℝ)))`

## Sibling prerequisites

- `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.local_unit_rep-a1.area_formula-a1.gram_area-a1`
- `root.minimizing_implies_stationary-a1.diffeo_pushforward-a1.piece_tangent_density-a1`
- `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.local_unit_rep-a1.wedge_orientation-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
