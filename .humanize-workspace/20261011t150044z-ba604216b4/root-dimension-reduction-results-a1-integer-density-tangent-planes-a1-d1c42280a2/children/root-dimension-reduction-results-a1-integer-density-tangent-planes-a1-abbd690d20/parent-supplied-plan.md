# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.two_dim_cone_density-a1.arc_continuation-a1.endpoint_plane-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-abbd690d20/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.two_dim_cone_density-a1.arc_continuation-a1`
- Child key: `endpoint_plane`
- Declaration: `Submission.idtp_tdc_acont_endpoint_plane`
- Exact Lean type: `∀ (P : ℕ) (C : GeometricCurrentOn (univ : Set (Euclid P)) 2) (Q : Submodule ℝ (Euclid P)) (z e : Euclid P) (k : ℕ) (φ₀ δ : ℝ), IsMinimizingIn C univ → BoundaryVanishes C → IsConeCurrent C → Module.finrank ℝ Q = 2 → z ∈ Q → e ∈ Q → ‖z‖ = 1 → ‖e‖ = 1 → inner ℝ z e = 0 → 0 < φ₀ → (∀ φ : ℝ, 0 < φ → φ < φ₀ → Real.cos φ • z + Real.sin φ • e ∈ C.support) → Real.cos φ₀ • z + Real.sin φ₀ • e ∈ C.support → 0 < δ → (∀ y ∈ C.support, y ∈ ball (Real.cos φ₀ • z + Real.sin φ₀ • e) δ → HasMassDensity C y k) → ∃ ε : ℝ, 0 < ε ∧ C.support ∩ ball (Real.cos φ₀ • z + Real.sin φ₀ • e) ε = (Q : Set (Euclid P)) ∩ ball (Real.cos φ₀ • z + Real.sin φ₀ • e) ε ∧ ∀ y ∈ C.support, y ∈ ball (Real.cos φ₀ • z + Real.sin φ₀ • e) ε → HasMassDensity C y k`

## Sibling prerequisites

- `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.two_dim_cone_density-a1.arc_continuation-a1.great_circle-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
