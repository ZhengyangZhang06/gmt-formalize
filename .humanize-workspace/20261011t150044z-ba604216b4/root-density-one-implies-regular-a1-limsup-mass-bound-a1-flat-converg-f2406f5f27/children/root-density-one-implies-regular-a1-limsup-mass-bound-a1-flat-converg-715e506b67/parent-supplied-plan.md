# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.skeleton_deformation-a1.series_limit-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-flat-converg-715e506b67/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.skeleton_deformation-a1`
- Child key: `series_limit`
- Declaration: `Submission.dor_lmb_fcd_sd_series_limit`
- Exact Lean type: `(∀ (P m : ℕ) (U : Set (Euclid P)) (X : ℕ → GeometricCurrentOn U (m + 1)), IsOpen U → (∀ r, IsIntegerMultiplicity (X r)) → ∑' r, (X r).mass ≠ ∞ → ∃ Y : GeometricCurrentOn U (m + 1), IsIntegerMultiplicity Y ∧ (∀ ω : TestFormOn U (m + 1), HasSum (fun r => X r ω) (Y ω)) ∧ Y.mass ≤ ∑' r, (X r).mass) → ∀ (P m : ℕ) (c : ℝ) (T : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)) (V E' A Kc : ℕ → GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)) (H : ℕ → GeometricCurrentOn (univ : Set (Euclid P)) (m + 2)) (Y L : ℕ → GeometricCurrentOn (univ : Set (Euclid P)) m) (F₁ F₂ : Set (Euclid P)), T.mass ≠ ∞ → T.boundary.mass ≠ ∞ → (∀ j, IsIntegerMultiplicity (V j)) → (∀ j, IsIntegerMultiplicity (H j)) → (∀ j, IsIntegerMultiplicity (E' j)) → (∀ N (ω : TestFormOn (univ : Set (Euclid P)) (m + 1)), ∑ j ∈ Finset.range (N + 1), V j ω - T ω + A N ω - ∑ j ∈ Finset.range (N + 1), (H j).boundary ω = ∑ j ∈ Finset.range (N + 1), E' j ω - Kc N ω) → (∀ N (ω : TestFormOn (univ : Set (Euclid P)) m), ∑ j ∈ Finset.range (N + 1), (V j).boundary ω = ∑ j ∈ Finset.range (N + 1), Y j ω - L N ω) → Tendsto (fun N => (A N).mass) atTop (𝓝 0) → Tendsto (fun N => (Kc N).mass) atTop (𝓝 0) → Tendsto (fun N => (L N).mass) atTop (𝓝 0) → ∑' j, (V j).mass ≤ ENNReal.ofReal c * T.mass → ∑' j, (H j).mass ≤ ENNReal.ofReal c * T.mass → ∑' j, (E' j).mass ≤ ENNReal.ofReal c * T.boundary.mass → ∑' j, (Y j).mass ≤ ENNReal.ofReal c * T.boundary.mass → (∀ j (ω : TestFormOn (univ : Set (Euclid P)) (m + 1)), Disjoint (tsupport (ω : DifferentialForm (Euclid P) (m + 1))) (F₁) → V j ω = 0) → (∀ j (ω : TestFormOn (univ : Set (Euclid P)) (m + 2)), Disjoint (tsupport (ω : DifferentialForm (Euclid P) (m + 2))) (F₂) → H j ω = 0) → (∀ j (ω : TestFormOn (univ : Set (Euclid P)) (m + 1)), Disjoint (tsupport (ω : DifferentialForm (Euclid P) (m + 1))) (F₂) → E' j ω = 0) → ∃ (Q : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)) (R₁ : GeometricCurrentOn (univ : Set (Euclid P)) (m + 2)) (S₁ : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)), IsIntegerMultiplicity Q ∧ IsIntegerMultiplicity R₁ ∧ IsIntegerMultiplicity S₁ ∧ (∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 1), T ω - Q ω = R₁.boundary ω + S₁ ω) ∧ Q.mass ≤ ENNReal.ofReal c * T.mass ∧ Q.boundary.mass ≤ ENNReal.ofReal c * T.boundary.mass ∧ R₁.mass ≤ ENNReal.ofReal c * T.mass ∧ S₁.mass ≤ ENNReal.ofReal c * T.boundary.mass ∧ (∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 1), Disjoint (tsupport (ω : DifferentialForm (Euclid P) (m + 1))) (F₁) → Q ω = 0) ∧ (∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 2), Disjoint (tsupport (ω : DifferentialForm (Euclid P) (m + 2))) (F₂) → R₁ ω = 0) ∧ ∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 1), Disjoint (tsupport (ω : DifferentialForm (Euclid P) (m + 1))) (F₂) → S₁ ω = 0`

## Sibling prerequisites

- `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.skeleton_deformation-a1.zero_neg-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
