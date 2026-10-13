# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.regular_set_dense-a1.constant_multiplicity_reduction-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-set-dense-a1-constant-multiplicity-reduction-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.regular_set_dense-a1`
- Child key: `constant_multiplicity_reduction`
- Declaration: `Submission.rsd_constant_multiplicity_reduction`
- Exact Lean type: `∀ (P n : ℕ) (U N : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n) (z₀ : Euclid P) (r : ℝ) (N₀ : ℕ), IsOpen U → IsMinimizingIn T (U ∩ N) → T.support ⊆ N → BoundaryVanishes T → R.Represents T → 0 < r → ball z₀ r ⊆ U → 0 < N₀ → (∀ᵐ x ∂R.measure, x ∈ ball z₀ r → R.mult x = N₀) → z₀ ∈ T.support → HasMassDensity T z₀ N₀ → ∃ T₀ : GeometricCurrentOn (ball z₀ r) n, IsMinimizingIn T₀ (ball z₀ r ∩ N) ∧ T₀.support ⊆ N ∧ BoundaryVanishes T₀ ∧ (∀ W : Set (Euclid P), IsOpen W → CompactlyContained W (ball z₀ r) → T₀.massOn W < ∞) ∧ z₀ ∈ T₀.support ∧ HasMassDensity T₀ z₀ 1 ∧ (z₀ ∈ regularSet T₀ → z₀ ∈ regularSet T)`

## Sibling prerequisites

- `root.regular_set_dense-a1.mass_eq_weight-a1`
- `root.regular_set_dense-a1.support_iff_weight_pos-a1`
- `root.regular_set_dense-a1.integer_combination-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
