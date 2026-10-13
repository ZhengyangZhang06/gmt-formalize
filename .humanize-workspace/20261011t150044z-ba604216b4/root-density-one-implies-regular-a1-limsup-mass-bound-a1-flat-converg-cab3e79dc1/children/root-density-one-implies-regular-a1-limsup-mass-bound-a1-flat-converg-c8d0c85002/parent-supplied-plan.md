# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.dilation-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-flat-converg-c8d0c85002/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1`
- Child key: `dilation`
- Declaration: `Submission.dor_lmb_fcd_dilation`
- Exact Lean type: `∀ P : ℕ, ∃ dil : ∀ k : ℕ, ℝ → GeometricCurrentOn (univ : Set (Euclid P)) k → GeometricCurrentOn (univ : Set (Euclid P)) k, ∀ (k : ℕ) (lam : ℝ), 0 < lam → (∀ X Y : GeometricCurrentOn (univ : Set (Euclid P)) k, dil k lam (X - Y) = dil k lam X - dil k lam Y) ∧ (∀ X : GeometricCurrentOn (univ : Set (Euclid P)) k, dil k lam⁻¹ (dil k lam X) = X) ∧ (∀ X : GeometricCurrentOn (univ : Set (Euclid P)) k, (dil k lam X).mass = ENNReal.ofReal (lam ^ k) * X.mass) ∧ (∀ X : GeometricCurrentOn (univ : Set (Euclid P)) k, IsIntegerMultiplicity X → IsIntegerMultiplicity (dil k lam X)) ∧ (∀ X : GeometricCurrentOn (univ : Set (Euclid P)) (k + 1), (dil (k + 1) lam X).boundary = dil k lam X.boundary) ∧ (∀ (X : GeometricCurrentOn (univ : Set (Euclid P)) k) (E : Set (Euclid P)), (∀ ω : TestFormOn (univ : Set (Euclid P)) k, Disjoint (tsupport (ω : DifferentialForm (Euclid P) k)) (E) → X ω = 0) → ∀ ω : TestFormOn (univ : Set (Euclid P)) k, Disjoint (tsupport (ω : DifferentialForm (Euclid P) k)) ((fun x => lam • x) '' E) → dil k lam X ω = 0) ∧ (∀ (X : GeometricCurrentOn (univ : Set (Euclid P)) k) (ω : TestFormOn (univ : Set (Euclid P)) k), ∃ η : TestFormOn (univ : Set (Euclid P)) k, (∀ x, (η : DifferentialForm (Euclid P) k) x = lam ^ k • (ω : DifferentialForm (Euclid P) k) (lam • x)) ∧ dil k lam X ω = X η) ∧ ∀ (A : Set (Euclid P)) (g : Euclid P → ℝ), ∫ y in (fun x => lam • x) '' A, g y ∂μHE[k] = lam ^ k * ∫ x in A, g (lam • x) ∂μHE[k]`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
