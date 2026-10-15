# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.cube_poincare-a1.bv_poincare-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-flat-converg-fb41bce637/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.cube_poincare-a1`
- Child key: `bv_poincare`
- Declaration: `Submission.dor_lmb_fcd_cp_bv_poincare`
- Exact Lean type: `∀ (m : ℕ) (u : Euclid (m + 1) → ℝ) (V δ : ℝ) (η : ℕ → Euclid (m + 1) → ℝ), IntegrableOn u {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} → (∀ g : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g → tsupport g ⊆ {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} → (∀ y, ‖g y‖ ≤ 1) → ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, u y * LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ g y) ≤ V) → 0 < δ → δ < 1 / 2 → (∀ k, ContDiff ℝ (⊤ : ℕ∞) (η k)) → (∀ k, HasCompactSupport (η k)) → (∀ k z, 0 ≤ η k z) → (∀ k z, η k (-z) = η k z) → (∀ k, ∫ z, η k z = 1) → (∀ k, support (η k) ⊆ ball (0 : Euclid (m + 1)) δ) → (∀ᵐ x ∂volume, Tendsto (fun k => (convolution (η k) (Set.indicator {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} u) (ContinuousLinearMap.lsmul ℝ ℝ) volume) x) atTop (𝓝 ((Set.indicator {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} u) x))) → ∫ x in {y : Euclid (m + 1) | ∀ i, δ < y i ∧ y i < 1 - δ}, ∫ y in {y : Euclid (m + 1) | ∀ i, δ < y i ∧ y i < 1 - δ}, |u x - u y| ≤ ((m : ℝ) + 1) * (1 - 2 * δ) * (volume {y : Euclid (m + 1) | ∀ i, δ < y i ∧ y i < 1 - δ}).toReal * V`

## Sibling prerequisites

- `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.cube_poincare-a1.smooth_poincare-a1`
- `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.cube_poincare-a1.mollified_variation-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
