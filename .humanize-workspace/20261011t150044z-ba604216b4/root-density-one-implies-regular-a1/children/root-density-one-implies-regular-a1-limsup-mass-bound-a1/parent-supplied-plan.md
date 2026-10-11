# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.limsup_mass_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1`
- Child key: `limsup_mass_bound`
- Declaration: `Submission.dor_minimizing_limsup_mass_bound`
- Exact Lean type: `∀ (n k ℓ : ℕ), ℓ ≤ k → 0 < n → ∀ (U N : Set (Euclid (n + k))) (Ts : ℕ → GeometricCurrentOn U n) (T : GeometricCurrentOn U n) (y : Euclid (n + k)), IsOpen U → IsEmbeddedSubmanifold 2 (n + ℓ) N → (closure N \ N) ∩ U = ∅ → (∀ j, IsMinimizingIn (Ts j) (U ∩ N)) → IsIntegerMultiplicity T → (∀ j, (Ts j).support ⊆ N) → (∀ j, BoundaryVanishes (Ts j)) → BoundaryVanishes T → (∀ j, ∀ R : IMRep U n, R.Represents (Ts j) → R.IsStationaryAlong N) → (∀ W : Set (Euclid (n + k)), IsOpen W → CompactlyContained W U → ⨆ j, (Ts j).massOn W < ∞) → WeaklyConvergesOn Ts T → y ∈ N ∩ U → ∃ r₁ c c₁ : ℝ, 0 < r₁ ∧ 0 ≤ c ∧ 0 ≤ c₁ ∧ ∀ ρ ε : ℝ, 0 < ε → ε < ρ → ρ < r₁ → limsup (fun j => (Ts j).massOn (ball y ρ)) atTop ≤ ENNReal.ofReal ((1 + c * ρ) ^ n) * T.massOn (ball y (ρ + ε)) + ENNReal.ofReal (c₁ * ρ ^ (n + 1))`

## Sibling prerequisites

- `root.density_one_implies_regular-a1.imrep_mass_and_support-a1`
- `root.density_one_implies_regular-a1.mean_curvature_monotonicity-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
