# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.cone_splitting-a1.split_off_spine-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-ac0f702949/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.cone_splitting-a1`
- Child key: `split_off_spine`
- Declaration: `Submission.idtp_fons_cs_split_off_spine`
- Exact Lean type: `∀ (P n : ℕ) (S : GeometricCurrentOn (univ : Set (Euclid P)) n) (R : IMRep (univ : Set (Euclid P)) n) (L : Submodule ℝ (Euclid P)), Module.finrank ℝ L < n → n ≤ P → IsMinimizingIn S univ → BoundaryVanishes S → IsConeCurrent S → (∀ v ∈ L, ∀ ω : TestFormOn (univ : Set (Euclid P)) n, currentEval (blowUp S (-v) 1 one_ne_zero) (ω : DifferentialForm (Euclid P) n) = S ω) → R.Represents S → (∀ᵐ x ∂R.measure, ∀ v ∈ L, (approxTangentPlane n R.carrier x).starProjection v = v) → ∃ (S₀ : GeometricCurrentOn (univ : Set (Euclid P)) (n - Module.finrank ℝ L)) (R₀ : IMRep (univ : Set (Euclid P)) (n - Module.finrank ℝ L)), R₀.Represents S₀ ∧ IsMinimizingIn S₀ (Lᗮ : Set (Euclid P)) ∧ BoundaryVanishes S₀ ∧ IsConeCurrent S₀ ∧ S₀.support ⊆ (Lᗮ : Set (Euclid P)) ∧ R₀.measure (Lᗮ : Set (Euclid P))ᶜ = 0 ∧ ∀ A : Set (Euclid P), MeasurableSet A → R.measure A = ∫⁻ t in (L : Set (Euclid P)), R₀.measure ((fun y => t + y) ⁻¹' A) ∂μHE[Module.finrank ℝ L]`

## Sibling prerequisites

- `root.dimension_reduction_results-a1.im_mass_measure-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
