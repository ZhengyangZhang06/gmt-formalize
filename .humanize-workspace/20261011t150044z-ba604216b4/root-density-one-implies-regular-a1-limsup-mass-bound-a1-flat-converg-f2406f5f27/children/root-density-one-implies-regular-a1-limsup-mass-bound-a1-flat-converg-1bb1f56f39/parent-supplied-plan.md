# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.skeleton_deformation-a1.shells-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-flat-converg-1bb1f56f39/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.skeleton_deformation-a1`
- Child key: `shells`
- Declaration: `Submission.dor_lmb_fcd_sd_shells`
- Exact Lean type: `∀ (P m : ℕ) (T : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)) (RT : IMRep (univ : Set (Euclid P)) (m + 1)) (RB : IMRep (univ : Set (Euclid P)) m) (K : Set (Euclid P)) (f : Euclid P → ℝ) (r : ℕ → ℝ) (Z : ℕ → GeometricCurrentOn (univ : Set (Euclid P)) m), RT.Represents T → RB.Represents T.boundary → IsClosed K → Continuous f → Antitone r → (∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 1), Disjoint (tsupport (ω : DifferentialForm (Euclid P) (m + 1))) (K) → T ω = 0) → (∀ j (ω : TestFormOn (univ : Set (Euclid P)) m), Z j ω = (∫ x in RT.carrier ∩ {x | f x < r j}, (RT.mult x : ℝ) * RT.orient x (exteriorDerivative (ω : DifferentialForm (Euclid P) m) x) ∂μHE[m + 1]) - ∫ x in RB.carrier ∩ {x | f x < r j}, (RB.mult x : ℝ) * RB.orient x ((ω : DifferentialForm (Euclid P) m) x) ∂μHE[m]) → ∃ (W A : ℕ → GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)) (D : ℕ → GeometricCurrentOn (univ : Set (Euclid P)) m), (∀ j, IsIntegerMultiplicity (W j)) ∧ (∀ j, IsIntegerMultiplicity (D j)) ∧ (∀ j (ω : TestFormOn (univ : Set (Euclid P)) (m + 1)), Disjoint (tsupport (ω : DifferentialForm (Euclid P) (m + 1))) (K ∩ {x | r j ≤ f x}) → W j ω = 0) ∧ (∀ j (ω : TestFormOn (univ : Set (Euclid P)) m), Disjoint (tsupport (ω : DifferentialForm (Euclid P) m)) (K ∩ {x | r j ≤ f x}) → D j ω = 0) ∧ (∀ j (ω : TestFormOn (univ : Set (Euclid P)) m), Disjoint (tsupport (ω : DifferentialForm (Euclid P) m)) (K ∩ {x | r j ≤ f x}) → Z j ω = 0) ∧ (∀ ω : TestFormOn (univ : Set (Euclid P)) m, (W 0).boundary ω = D 0 ω - Z 0 ω) ∧ (∀ j (ω : TestFormOn (univ : Set (Euclid P)) m), (W (j + 1)).boundary ω = D (j + 1) ω + Z j ω - Z (j + 1) ω) ∧ (∀ N (ω : TestFormOn (univ : Set (Euclid P)) (m + 1)), ∑ j ∈ Finset.range (N + 1), W j ω = T ω - A N ω) ∧ (W 0).mass = RT.measure {x | r 0 ≤ f x} ∧ (∀ j, (W (j + 1)).mass = RT.measure {x | r (j + 1) ≤ f x ∧ f x < r j}) ∧ (D 0).mass = RB.measure {x | r 0 ≤ f x} ∧ (∀ j, (D (j + 1)).mass = RB.measure {x | r (j + 1) ≤ f x ∧ f x < r j}) ∧ ∀ N, (A N).mass = RT.measure {x | f x < r N}`

## Sibling prerequisites

- `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.skeleton_deformation-a1.im_restrict-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
