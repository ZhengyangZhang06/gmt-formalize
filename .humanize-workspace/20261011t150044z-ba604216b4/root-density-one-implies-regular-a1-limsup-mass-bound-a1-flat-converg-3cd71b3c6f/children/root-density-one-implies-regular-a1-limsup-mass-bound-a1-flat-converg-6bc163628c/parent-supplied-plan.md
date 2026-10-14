# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.im_pushforward-a1.image_series_im-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-flat-converg-6bc163628c/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.im_pushforward-a1`
- Child key: `image_series_im`
- Declaration: `Submission.dor_lmb_fcd_imp_image_series_im`
- Exact Lean type: `(∀ (P m : ℕ) (U : Set (Euclid P)) (X : ℕ → GeometricCurrentOn U (m + 1)), IsOpen U → (∀ r, IsIntegerMultiplicity (X r)) → ∑' r, (X r).mass ≠ ∞ → ∃ Y : GeometricCurrentOn U (m + 1), IsIntegerMultiplicity Y ∧ (∀ ω : TestFormOn U (m + 1), HasSum (fun r => X r ω) (Y ω)) ∧ Y.mass ≤ ∑' r, (X r).mass) → ((∀ (P n : ℕ) (U M M' : Set (Euclid P)), IsOpen U → MeasurableSet M → MeasurableSet M' → M ⊆ M' → M' ⊆ U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (M' ∩ K) ≠ ∞) → ∀ᵐ x ∂(μHE[n].restrict M), ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n M x Q ↔ HasApproximateTangentSpaceAt n M' x Q) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (E : Set (Euclid P)), IsOpen U → MeasurableSet E → ∃ (A : GeometricCurrentOn U n) (R' : IMRep U n), R'.Represents A ∧ R'.carrier = R.carrier ∩ E ∧ R'.mult = R.mult ∧ R'.orient = R.orient) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (A B : GeometricCurrentOn U n), IsOpen U → IsIntegerMultiplicity A → IsIntegerMultiplicity B → IsIntegerMultiplicity (A - B)) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n), ∀ᵐ x ∂(μHE[n].restrict R.carrier), ∀ α : Covector (Euclid P) n, |R.orient x α| ≤ covectorEuclideanNorm α)) → ∀ (N N' k : ℕ) (G : ℕ → Euclid (k + 1) → Euclid N) (B : ℕ → Set (Euclid (k + 1))) (w : ℕ → Euclid (k + 1) → ℝ) (F : Euclid N → Euclid N') (Λ : NNReal), (∀ i, ∃ L : NNReal, LipschitzWith L (G i)) → (∀ i, MeasurableSet (B i)) → (∀ i, ∀ u ∈ B i, DifferentiableAt ℝ (G i) u) → (∀ i, Measurable (w i)) → (∀ i u, ∃ z : ℤ, w i u = z) → (∀ i, ∀ u ∈ B i, w i u ≠ 0) → (∀ i, IntegrableOn (w i) (B i)) → ∑' i, ∫⁻ u in B i, ‖w i u‖ₑ * ENNReal.ofReal (Real.sqrt (Matrix.det (Matrix.of fun a b : Fin (k + 1) => inner ℝ (fderiv ℝ (G i) u (EuclideanSpace.single a (1 : ℝ))) (fderiv ℝ (G i) u (EuclideanSpace.single b (1 : ℝ)))))) ≠ ∞ → LipschitzWith Λ F → ∃ Y : GeometricCurrentOn (univ : Set (Euclid N')) (k + 1), IsIntegerMultiplicity Y ∧ (∀ ω : TestFormOn (univ : Set (Euclid N')) (k + 1), HasSum (fun i => ∫ u in B i, w i u * (ω : DifferentialForm (Euclid N') (k + 1)) ((F ∘ G i) u) (fun a => fderiv ℝ (F ∘ G i) u (EuclideanSpace.single a (1 : ℝ)))) (Y ω)) ∧ ∀ (ω : TestFormOn (univ : Set (Euclid N')) (k + 1)) (c : ℝ), 0 < c → (∀ x, covectorEuclideanNorm ((ω : DifferentialForm (Euclid N') (k + 1)) x) ≤ c) → ∀ i, |∫ u in B i, w i u * (ω : DifferentialForm (Euclid N') (k + 1)) ((F ∘ G i) u) (fun a => fderiv ℝ (F ∘ G i) u (EuclideanSpace.single a (1 : ℝ)))| ≤ c * (Λ : ℝ) ^ (k + 1) * (∫⁻ u in B i, ‖w i u‖ₑ * ENNReal.ofReal (Real.sqrt (Matrix.det (Matrix.of fun a b : Fin (k + 1) => inner ℝ (fderiv ℝ (G i) u (EuclideanSpace.single a (1 : ℝ))) (fderiv ℝ (G i) u (EuclideanSpace.single b (1 : ℝ))))))).toReal`

## Sibling prerequisites

- `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.im_pushforward-a1.piece_current-a1`
- `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.im_pushforward-a1.regular_partition-a1`
- `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.im_pushforward-a1.lipschitz_jacobian_locality-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
