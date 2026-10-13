# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.limsup_mass_bound-a1.projected_comparison-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-projected-comparison-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1`
- Child key: `projected_comparison`
- Declaration: `Submission.dor_lmb_projected_competitor_comparison`
- Exact Lean type: `(∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), IsOpen U → R.Represents T → (∀ W : Set (Euclid P), IsOpen W → T.massOn W = R.measure W) ∧ T.support = U ∩ R.measure.support) → ∀ (P d n : ℕ) (U N : Set (Euclid P)) (Z X Y : GeometricCurrentOn U n) (RZ RY : IMRep U n) (proj : Euclid P → Euclid P) (y : Euclid P) (r c ρ t : ℝ), IsOpen U → 0 < n → IsEmbeddedSubmanifold 2 d N → IsMinimizingIn Z (U ∩ N) → Z.support ⊆ N → BoundaryVanishes Z → RZ.Represents Z → IsIntegerMultiplicity X → BoundaryVanishes X → (∀ ω : TestFormOn U n, Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) (closedBall y t) → X ω = 0) → (∀ ω : TestFormOn U n, Y ω = Z ω + X ω) → RY.Represents Y → y ∈ N → 0 ≤ c → 0 < ρ → 3 * ρ < r → 4 * c * ρ ≤ 1 → t < 2 * ρ → closedBall y (3 * ρ) ⊆ U → ContDiffOn ℝ 1 proj (ball y r) → MapsTo proj (ball y r) N → (∀ x ∈ N ∩ ball y r, proj x = x) → (∀ x ∈ N ∩ ball y r, ∀ v ∈ tangentSpace N x, fderiv ℝ proj x v = v) → (∀ x ∈ ball y r, ‖fderiv ℝ proj x‖ ≤ 1 + c * dist x y) → RZ.measure (closedBall y t) ≤ ENNReal.ofReal ((1 + 3 * c * ρ) ^ n) * RY.measure (closedBall y t) + ENNReal.ofReal ((1 + 3 * c * ρ) ^ n - 1) * RZ.measure (ball y (3 * ρ))`

## Sibling prerequisites

- `root.density_one_implies_regular-a1.limsup_mass_bound-a1.tangent_locality-a1`
- `root.density_one_implies_regular-a1.limsup_mass_bound-a1.int_combination-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
