# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_constant_density_planar-a1.stationary_cone_sheet_planar-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-3876084c61/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_constant_density_planar-a1`
- Child key: `stationary_cone_sheet_planar`
- Declaration: `Submission.idtp_ccd_stationary_cone_sheet_planar`
- Exact Lean type: `∀ (P : ℕ) (M : Set (Euclid P)) (p : Euclid P) (ρ : ℝ), IsEmbeddedSubmanifold 1 2 M → p ∈ M → p ≠ 0 → 0 < ρ → (∀ x ∈ M ∩ ball p ρ, ∀ t : ℝ, 0 < t → t • x ∈ ball p ρ → t • x ∈ M) → (∀ X : Euclid P → Euclid P, ContDiff ℝ 1 X → HasCompactSupport X → tsupport X ⊆ ball p ρ → ∫ x in M ∩ ball p ρ, LinearMap.trace ℝ (Euclid P) ((Submodule.span ℝ (tangentSpace M x)).starProjection.toLinearMap ∘ₗ (fderiv ℝ X x).toLinearMap) ∂μHE[2] = 0) → ∃ (δ : ℝ) (Q : Submodule ℝ (Euclid P)), 0 < δ ∧ Module.finrank ℝ Q = 2 ∧ p ∈ Q ∧ M ∩ ball p δ = (Q : Set (Euclid P)) ∩ ball p δ`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
