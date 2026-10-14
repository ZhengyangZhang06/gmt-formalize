# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.pushforward_calculus-a1.toolkit_push-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-flat-converg-a543079f94/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.pushforward_calculus-a1`
- Child key: `toolkit_push`
- Declaration: `Submission.dor_lmb_fcdp_toolkit_push`
- Exact Lean type: `((∀ (P k : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid P)) k) (R : IMRep (univ : Set (Euclid P)) k) (E : Set (Euclid P)), R.Represents X → IsCompact E → (∀ ω : TestFormOn (univ : Set (Euclid P)) k, Disjoint (tsupport (ω : DifferentialForm (Euclid P) k)) E → X ω = 0) → μHE[k] (R.carrier \ E) = 0 ∧ X.mass = R.measure univ ∧ R.measure univ ≠ ∞ ∧ ∀ γ γ' : DifferentialForm (Euclid P) k, EqOn γ γ' E → R.action γ = R.action γ') ∧ (∀ (N m : ℕ) (α : Covector (Euclid N) m) (v : Fin m → Euclid N), |α v| ≤ covectorEuclideanNorm α * ∏ i, ‖v i‖) ∧ (∀ (P k : ℕ) (U : Set (Euclid P)) (R : IMRep U k) (γ : DifferentialForm (Euclid P) k) (c : ℝ), R.measure univ ≠ ∞ → 0 ≤ c → (∀ᵐ x ∂(μHE[k].restrict R.carrier), ∀ τ : Fin k → Euclid P, Orthonormal ℝ τ → |γ x τ| ≤ c) → |R.action γ| ≤ c * (R.measure univ).toReal) ∧ (∀ (N N' : ℕ) (Λ : NNReal) (F : Euclid N → Euclid N'), LipschitzWith Λ F → ∃ Fs : ℕ → Euclid N → Euclid N', (∀ j, ContDiff ℝ (⊤ : ℕ∞) (Fs j)) ∧ (∀ j, LipschitzWith Λ (Fs j)) ∧ TendstoUniformly Fs F atTop) ∧ ∀ (P : ℕ) (E : Set (Euclid P)), IsCompact E → ∃ (χ : Euclid P → ℝ) (W : Set (Euclid P)), ContDiff ℝ (⊤ : ℕ∞) χ ∧ HasCompactSupport χ ∧ (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧ IsOpen W ∧ E ⊆ W ∧ ∀ x ∈ W, χ x = 1) ∧ ((∀ (N N' k : ℕ) (R : IMRep (univ : Set (Euclid N)) k), R.measure univ ≠ ∞ → ∃ Y : (Euclid N → Euclid N') → GeometricCurrentOn (univ : Set (Euclid N')) k, (∀ (F : Euclid N → Euclid N') (Λ : NNReal), LipschitzWith Λ F → IsIntegerMultiplicity (Y F) ∧ ∀ Fs : ℕ → Euclid N → Euclid N', (∀ j, ContDiff ℝ 1 (Fs j)) → (∀ j, LipschitzWith Λ (Fs j)) → TendstoUniformly Fs F atTop → ∀ ω : TestFormOn (univ : Set (Euclid N')) k, Tendsto (fun j => R.action (fun x => ((ω : DifferentialForm (Euclid N') k) (Fs j x)).compContinuousLinearMap (fderiv ℝ (Fs j) x))) atTop (𝓝 (Y F ω))) ∧ ∀ (F F' : Euclid N → Euclid N') (Λ : NNReal), LipschitzWith Λ F → LipschitzWith Λ F' → (∀ᵐ x ∂(μHE[k].restrict R.carrier), F x = F' x) → Y F = Y F') → ∀ P : ℕ, ∃ push : ∀ k : ℕ, (Euclid P → Euclid P) → GeometricCurrentOn (univ : Set (Euclid P)) k → GeometricCurrentOn (univ : Set (Euclid P)) k, ∀ (k : ℕ) (Λ : NNReal) (F : Euclid P → Euclid P) (E : Set (Euclid P)) (X : GeometricCurrentOn (univ : Set (Euclid P)) k), LipschitzWith Λ F → IsCompact E → IsIntegerMultiplicity X → (∀ ω : TestFormOn (univ : Set (Euclid P)) k, Disjoint (tsupport (ω : DifferentialForm (Euclid P) k)) E → X ω = 0) → IsIntegerMultiplicity (push k F X) ∧ (∀ F' : Euclid P → Euclid P, LipschitzWith Λ F' → EqOn F F' E → push k F X = push k F' X) ∧ (∀ (Fs : ℕ → Euclid P → Euclid P) (ω : TestFormOn (univ : Set (Euclid P)) k) (ηs : ℕ → TestFormOn (univ : Set (Euclid P)) k), (∀ j, ContDiff ℝ 1 (Fs j)) → (∀ j, LipschitzWith Λ (Fs j)) → TendstoUniformly Fs F atTop → (∀ j, ∀ x ∈ E, (ηs j : DifferentialForm (Euclid P) k) x = ((ω : DifferentialForm (Euclid P) k) (Fs j x)).compContinuousLinearMap (fderiv ℝ (Fs j) x)) → Tendsto (fun j => X (ηs j)) atTop (𝓝 (push k F X ω))) ∧ (push k F X).mass ≤ (Λ : ℝ≥0∞) ^ k * X.mass ∧ ∀ ω : TestFormOn (univ : Set (Euclid P)) k, Disjoint (tsupport (ω : DifferentialForm (Euclid P) k)) (F '' E) → push k F X ω = 0)`

## Sibling prerequisites

- `root.density_one_implies_regular-a1.imrep_mass_and_support-a1`
- `root.minimizing_implies_stationary-a1.covector_gram_bounds-a1`
- `root.minimizing_implies_stationary-a1.diffeo_pushforward-a1.orientation_pushforward-a1.gram_schmidt_frame-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
