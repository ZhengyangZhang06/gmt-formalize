# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.pushforward_calculus-a1.homot_operator-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-flat-converg-a8facf8148/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.pushforward_calculus-a1`
- Child key: `homot_operator`
- Declaration: `Submission.dor_lmb_fcdp_homot_operator`
- Exact Lean type: `(∀ (N N' k : ℕ) (R : IMRep (univ : Set (Euclid N)) k), R.measure univ ≠ ∞ → ∃ Y : (Euclid N → Euclid N') → GeometricCurrentOn (univ : Set (Euclid N')) k, (∀ (F : Euclid N → Euclid N') (Λ : NNReal), LipschitzWith Λ F → IsIntegerMultiplicity (Y F) ∧ ∀ Fs : ℕ → Euclid N → Euclid N', (∀ j, ContDiff ℝ 1 (Fs j)) → (∀ j, LipschitzWith Λ (Fs j)) → TendstoUniformly Fs F atTop → ∀ ω : TestFormOn (univ : Set (Euclid N')) k, Tendsto (fun j => R.action (fun x => ((ω : DifferentialForm (Euclid N') k) (Fs j x)).compContinuousLinearMap (fderiv ℝ (Fs j) x))) atTop (𝓝 (Y F ω))) ∧ ∀ (F F' : Euclid N → Euclid N') (Λ : NNReal), LipschitzWith Λ F → LipschitzWith Λ F' → (∀ᵐ x ∂(μHE[k].restrict R.carrier), F x = F' x) → Y F = Y F') → ∀ P : ℕ, ∃ homot : ∀ k : ℕ, (Euclid P → Euclid P) → (Euclid P → Euclid P) → GeometricCurrentOn (univ : Set (Euclid P)) k → GeometricCurrentOn (univ : Set (Euclid P)) (k + 1), ∀ (k : ℕ) (Λ : NNReal) (F G : Euclid P → Euclid P) (E : Set (Euclid P)) (X : GeometricCurrentOn (univ : Set (Euclid P)) k), LipschitzWith Λ F → LipschitzWith Λ G → IsCompact E → IsIntegerMultiplicity X → (∀ ω : TestFormOn (univ : Set (Euclid P)) k, Disjoint (tsupport (ω : DifferentialForm (Euclid P) k)) E → X ω = 0) → IsIntegerMultiplicity (homot k F G X) ∧ (∀ F' G' : Euclid P → Euclid P, LipschitzWith Λ F' → LipschitzWith Λ G' → EqOn F F' E → EqOn G G' E → homot k F G X = homot k F' G' X) ∧ (∀ (Fs Gs : ℕ → Euclid P → Euclid P) (ω : TestFormOn (univ : Set (Euclid P)) (k + 1)) (ηs : ℕ → TestFormOn (univ : Set (Euclid P)) k), (∀ j, ContDiff ℝ 1 (Fs j)) → (∀ j, ContDiff ℝ 1 (Gs j)) → (∀ j, LipschitzWith Λ (Fs j)) → (∀ j, LipschitzWith Λ (Gs j)) → TendstoUniformly Fs F atTop → TendstoUniformly Gs G atTop → (∀ j, ∀ x ∈ E, (ηs j : DifferentialForm (Euclid P) k) x = ∫ t in (0 : ℝ)..1, (((ω : DifferentialForm (Euclid P) (k + 1)) (Fs j x + t • (Gs j x - Fs j x))).curryLeft (Gs j x - Fs j x)).compContinuousLinearMap (fderiv ℝ (Fs j) x + t • (fderiv ℝ (Gs j) x - fderiv ℝ (Fs j) x))) → Tendsto (fun j => X (ηs j)) atTop (𝓝 (homot k F G X ω))) ∧ (∀ ω : TestFormOn (univ : Set (Euclid P)) (k + 1), Disjoint (tsupport (ω : DifferentialForm (Euclid P) (k + 1))) {y : Euclid P | ∃ x ∈ E, ∃ t ∈ Icc (0 : ℝ) 1, y = F x + t • (G x - F x)} → homot k F G X ω = 0) ∧ ∀ δ : ℝ, (∀ x ∈ E, dist (F x) (G x) ≤ δ) → (homot k F G X).mass ≤ ENNReal.ofReal δ * (2 * (Λ : ℝ≥0∞)) ^ k * X.mass`

## Sibling prerequisites

- `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.pushforward_calculus-a1.toolkit_push-a1`
- `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.pushforward_calculus-a1.product_imrep-a1`
- `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.pushforward_calculus-a1.homotopy_maps-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
