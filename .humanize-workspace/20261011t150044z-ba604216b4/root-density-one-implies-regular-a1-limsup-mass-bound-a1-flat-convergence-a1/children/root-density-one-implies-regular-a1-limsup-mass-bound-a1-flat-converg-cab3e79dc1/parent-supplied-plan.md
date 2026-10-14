# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-flat-converg-cab3e79dc1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1`
- Child key: `deformation`
- Declaration: `Submission.dor_lmb_fc_deformation`
- Exact Lean type: `((∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), IsOpen U → R.Represents T → (∀ W : Set (Euclid P), IsOpen W → T.massOn W = R.measure W) ∧ T.support = U ∩ R.measure.support) → ∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U (n + 1)) (RT : IMRep U (n + 1)) (RB : IMRep U n) (f : Euclid P → ℝ) (L : NNReal), IsOpen U → RT.Represents T → RB.Represents T.boundary → LipschitzWith L f → ∃ Ps : ℝ → GeometricCurrentOn U n, (∀ W : Set (Euclid P), IsOpen W → AEMeasurable (fun t => (Ps t).massOn W) ∧ ∫⁻ t, (Ps t).massOn W ≤ (L : ℝ≥0∞) * T.massOn W) ∧ ∀ᵐ t, IsIntegerMultiplicity (Ps t) ∧ (∀ ω : TestFormOn U n, Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) (f ⁻¹' {t}) → Ps t ω = 0) ∧ ∀ ω : TestFormOn U n, Ps t ω = (∫ x in RT.carrier ∩ {x | f x < t}, (RT.mult x : ℝ) * RT.orient x (exteriorDerivative (ω : DifferentialForm (Euclid P) n) x) ∂μHE[n + 1]) - ∫ x in RB.carrier ∩ {x | f x < t}, (RB.mult x : ℝ) * RB.orient x ((ω : DifferentialForm (Euclid P) n) x) ∂μHE[n]) → ∀ (P m : ℕ), m + 1 < P → ∃ c : ℝ, 0 ≤ c ∧ ∀ (ρ : ℝ) (K : Set (Euclid P)) (T : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)), 0 < ρ → IsCompact K → IsIntegerMultiplicity T → IsIntegerMultiplicity T.boundary → (∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 1), Disjoint (tsupport (ω : DifferentialForm (Euclid P) (m + 1))) K → T ω = 0) → ∃ (s : Finset ((Fin P → ℤ) × (Fin (m + 1) → Fin P))) (β : (Fin P → ℤ) × (Fin (m + 1) → Fin P) → ℤ) (Pc : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)) (R : GeometricCurrentOn (univ : Set (Euclid P)) (m + 2)) (S : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)), (∀ p ∈ s, StrictMono p.2) ∧ (∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 1), Pc ω = ∑ p ∈ s, (β p : ℝ) * ∫ x in {x : Euclid P | ∀ i : Fin P, (i ∈ Set.range p.2 → ρ * p.1 i ≤ x i ∧ x i ≤ ρ * (p.1 i + 1)) ∧ (i ∉ Set.range p.2 → x i = ρ * p.1 i)}, (ω : DifferentialForm (Euclid P) (m + 1)) x (fun k => EuclideanSpace.single (p.2 k) (1 : ℝ)) ∂μHE[m + 1]) ∧ IsIntegerMultiplicity R ∧ IsIntegerMultiplicity S ∧ (∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 1), T ω - Pc ω = R.boundary ω + S ω) ∧ (∑ p ∈ s, ((β p).natAbs : ℝ≥0∞)) * ENNReal.ofReal (ρ ^ (m + 1)) ≤ ENNReal.ofReal c * T.mass ∧ R.mass ≤ ENNReal.ofReal (c * ρ) * T.mass ∧ S.mass ≤ ENNReal.ofReal (c * ρ) * T.boundary.mass ∧ (∀ p ∈ s, {x : Euclid P | ∀ i : Fin P, (i ∈ Set.range p.2 → ρ * p.1 i ≤ x i ∧ x i ≤ ρ * (p.1 i + 1)) ∧ (i ∉ Set.range p.2 → x i = ρ * p.1 i)} ⊆ cthickening (2 * Real.sqrt P * ρ) K) ∧ (∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 2), Disjoint (tsupport (ω : DifferentialForm (Euclid P) (m + 2))) (cthickening (2 * Real.sqrt P * ρ) K) → R ω = 0) ∧ ∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 1), Disjoint (tsupport (ω : DifferentialForm (Euclid P) (m + 1))) (cthickening (2 * Real.sqrt P * ρ) K) → S ω = 0`

## Sibling prerequisites

- `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.im_series-a1`
- `root.density_one_implies_regular-a1.imrep_mass_and_support-a1`
- `root.compactness_of_minimizing_currents-a1.im_calculus-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
