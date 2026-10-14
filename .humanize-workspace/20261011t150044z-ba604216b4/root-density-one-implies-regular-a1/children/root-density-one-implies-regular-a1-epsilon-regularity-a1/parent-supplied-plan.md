# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.epsilon_regularity-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1`
- Child key: `epsilon_regularity`
- Declaration: `Submission.dor_stationary_cycle_epsilon_regularity`
- Exact Lean type: `∀ (n k ℓ : ℕ), ℓ ≤ k → 0 < n → ∀ (U N : Set (Euclid (n + k))) (y₀ : Euclid (n + k)), IsOpen U → IsEmbeddedSubmanifold 2 (n + ℓ) N → (closure N \ N) ∩ U = ∅ → y₀ ∈ N ∩ U → ∃ r₀ δ : ℝ, 0 < r₀ ∧ 0 < δ ∧ ∀ (T : GeometricCurrentOn U n) (R : IMRep U n), R.Represents T → T.support ⊆ N → BoundaryVanishes T → R.IsStationaryAlong N → ∀ z ∈ T.support, dist z y₀ < r₀ → ∀ ρ : ℝ, 0 < ρ → ρ ≤ r₀ → T.massOn (ball z ρ) ≤ ENNReal.ofReal (1 + δ) * unitBallVolume n * ENNReal.ofReal (ρ ^ n) → z ∈ regularSet T`

## Sibling prerequisites

- `root.density_one_implies_regular-a1.imrep_mass_and_support-a1`
- `root.density_one_implies_regular-a1.mean_curvature_monotonicity-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
