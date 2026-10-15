# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.localize-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-flat-converg-8923ace5f0/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1`
- Child key: `localize`
- Declaration: `Submission.dor_lmb_fc_localize`
- Exact Lean type: `((∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), IsOpen U → R.Represents T → (∀ W : Set (Euclid P), IsOpen W → T.massOn W = R.measure W) ∧ T.support = U ∩ R.measure.support) → ∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U (n + 1)) (RT : IMRep U (n + 1)) (RB : IMRep U n) (f : Euclid P → ℝ) (L : NNReal), IsOpen U → RT.Represents T → RB.Represents T.boundary → LipschitzWith L f → ∃ Ps : ℝ → GeometricCurrentOn U n, (∀ W : Set (Euclid P), IsOpen W → AEMeasurable (fun t => (Ps t).massOn W) ∧ ∫⁻ t, (Ps t).massOn W ≤ (L : ℝ≥0∞) * T.massOn W) ∧ ∀ᵐ t, IsIntegerMultiplicity (Ps t) ∧ (∀ ω : TestFormOn U n, Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) (f ⁻¹' {t}) → Ps t ω = 0) ∧ ∀ ω : TestFormOn U n, Ps t ω = (∫ x in RT.carrier ∩ {x | f x < t}, (RT.mult x : ℝ) * RT.orient x (exteriorDerivative (ω : DifferentialForm (Euclid P) n) x) ∂μHE[n + 1]) - ∫ x in RB.carrier ∩ {x | f x < t}, (RB.mult x : ℝ) * RB.orient x ((ω : DifferentialForm (Euclid P) n) x) ∂μHE[n]) → ∀ (P m : ℕ) (U W : Set (Euclid P)) (Ts : ℕ → GeometricCurrentOn U (m + 1)) (T : GeometricCurrentOn U (m + 1)), IsOpen U → (∀ j, IsIntegerMultiplicity (Ts j)) → IsIntegerMultiplicity T → (∀ j, (Ts j).boundary = 0) → (∀ V : Set (Euclid P), IsOpen V → CompactlyContained V U → ⨆ j, (Ts j).massOn V < ∞) → WeaklyConvergesOn Ts T → W.Nonempty → CompactlyContained W U → ∃ (φ : ℕ → ℕ) (K : Set (Euclid P)) (Λ : ℝ≥0∞) (Ts' : ℕ → GeometricCurrentOn U (m + 1)) (T' : GeometricCurrentOn U (m + 1)), StrictMono φ ∧ IsCompact K ∧ K ⊆ U ∧ Λ ≠ ∞ ∧ (∀ j, IsIntegerMultiplicity (Ts' j)) ∧ (∀ j, IsIntegerMultiplicity (Ts' j).boundary) ∧ IsIntegerMultiplicity T' ∧ (∀ j (ω : TestFormOn U (m + 1)), Disjoint (tsupport (ω : DifferentialForm (Euclid P) (m + 1))) K → Ts' j ω = 0) ∧ (∀ j, (Ts' j).mass ≤ Λ ∧ (Ts' j).boundary.mass ≤ Λ) ∧ WeaklyConvergesOn Ts' T' ∧ (∀ j (ω : TestFormOn U (m + 1)), tsupport (ω : DifferentialForm (Euclid P) (m + 1)) ⊆ W → Ts' j ω = Ts (φ j) ω) ∧ ∀ ω : TestFormOn U (m + 1), tsupport (ω : DifferentialForm (Euclid P) (m + 1)) ⊆ W → T' ω = T ω`

## Sibling prerequisites

- `root.density_one_implies_regular-a1.imrep_mass_and_support-a1`
- `root.compactness_of_minimizing_currents-a1.im_calculus-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
