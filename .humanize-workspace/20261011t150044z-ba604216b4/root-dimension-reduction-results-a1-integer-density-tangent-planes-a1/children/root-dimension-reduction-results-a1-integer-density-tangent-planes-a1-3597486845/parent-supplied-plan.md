# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_constant_density_planar-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-3597486845/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1`
- Child key: `cone_constant_density_planar`
- Declaration: `Submission.idtp_cone_constant_density_planar`
- Exact Lean type: `∀ (P : ℕ) (C : GeometricCurrentOn (univ : Set (Euclid P)) 2) (p : Euclid P) (k : ℕ) (δ : ℝ), IsMinimizingIn C univ → BoundaryVanishes C → IsConeCurrent C → p ∈ C.support → p ≠ 0 → 0 < δ → (∀ y ∈ C.support, y ∈ ball p δ → HasMassDensity C y k) → ∃ (δ' : ℝ) (Q : Submodule ℝ (Euclid P)), 0 < δ' ∧ Module.finrank ℝ Q = 2 ∧ p ∈ Q ∧ C.support ∩ ball p δ' = (Q : Set (Euclid P)) ∩ ball p δ' ∧ ∀ W : Set (Euclid P), IsOpen W → W ⊆ ball p δ' → C.massOn W = (k : ℝ≥0∞) * μHE[2] (W ∩ (Q : Set (Euclid P)))`

## Sibling prerequisites

- `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.density_eq_multiplicity_ae-a1`
- `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.planar_constancy-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
