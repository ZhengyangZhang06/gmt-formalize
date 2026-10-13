# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.cone_class-a1.monotonicity_bounds-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-8bcfcf93a4/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.cone_class-a1`
- Child key: `monotonicity_bounds`
- Declaration: `Submission.idtp_fons_cc_monotonicity_bounds`
- Exact Lean type: `(∀ (P n d : ℕ) (U N : Set (Euclid P)) (T : GeometricCurrentOn U n), 1 ≤ n → n ≤ d → d ≤ P → IsOpen U → IsEmbeddedSubmanifold 2 d N → (closure N \ N) ∩ U = ∅ → IsMinimizingIn T (U ∩ N) → T.support ⊆ U ∩ N → BoundaryVanishes T → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → ∃ Λ : ℝ, 0 ≤ Λ ∧ ∀ (y : Euclid P) (R : ℝ), closedBall y R ⊆ K → MonotoneOn (fun ρ : ℝ => ENNReal.ofReal (Real.exp (Λ * ρ) / ρ ^ n) * T.massOn (ball y ρ)) (Ioo 0 R)) ∧ (N = univ → ∀ (y : Euclid P) (R : ℝ), ball y R ⊆ U → MonotoneOn (fun ρ : ℝ => ENNReal.ofReal (1 / ρ ^ n) * T.massOn (ball y ρ)) (Ioo 0 R)) ∧ (∃ Θ : Euclid P → ℝ, (∀ y ∈ U, HasMassDensity T y (Θ y)) ∧ UpperSemicontinuousOn Θ U) ∧ ∀ y ∈ T.support, ∀ θ : ℝ, HasMassDensity T y θ → 1 ≤ θ) → (∀ (P n d : ℕ) (U N : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n) (K : Set (Euclid P)), 1 ≤ n → n ≤ d → d ≤ P → IsOpen U → IsEmbeddedSubmanifold 2 d N → (closure N \ N) ∩ U = ∅ → IsMinimizingIn T (U ∩ N) → T.support ⊆ U ∩ N → BoundaryVanishes T → R.Represents T → IsCompact K → K ⊆ U → ∃ Λ : ℝ, 0 ≤ Λ ∧ ∀ p : Euclid P, (∀ ε : ℝ, 0 < ε → R.measure (ball p ε) ≠ 0) → ∀ σ ρ : ℝ, closedBall p ρ ⊆ K → 0 < σ → σ < ρ → ENNReal.ofReal (Real.exp (-(Λ * σ))) * (unitBallVolume n * ENNReal.ofReal (σ ^ n)) ≤ R.measure (ball p σ)) ∧ ∀ (P n : ℕ) (S : GeometricCurrentOn (univ : Set (Euclid P)) n) (R : IMRep (univ : Set (Euclid P)) n), 1 ≤ n → n ≤ P → IsMinimizingIn S univ → BoundaryVanishes S → R.Represents S → (∀ w : Euclid P, (∀ ε : ℝ, 0 < ε → R.measure (ball w ε) ≠ 0) → ∀ ρ : ℝ, 0 < ρ → unitBallVolume n * ENNReal.ofReal (ρ ^ n) ≤ R.measure (ball w ρ)) ∧ (R.measure univ = 0 ∨ R.measure univ = ∞) ∧ ∀ (w : Euclid P) (θ : ℝ), HasMassDensity S w θ ↔ θ = (limsup (fun ρ : ℝ => R.measure (ball w ρ) / (unitBallVolume n * ENNReal.ofReal (ρ ^ n))) (𝓝[>] 0)).toReal`

## Sibling prerequisites

- `root.dimension_reduction_results-a1.im_mass_measure-a1`
- `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.cone_class-a1.ambient_calculus-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
