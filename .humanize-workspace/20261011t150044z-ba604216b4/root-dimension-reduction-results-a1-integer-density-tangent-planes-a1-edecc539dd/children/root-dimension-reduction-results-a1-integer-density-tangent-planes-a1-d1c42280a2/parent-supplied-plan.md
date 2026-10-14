# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.two_dim_cone_density-a1.arc_continuation-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-d1c42280a2/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.two_dim_cone_density-a1`
- Child key: `arc_continuation`
- Declaration: `Submission.idtp_tdc_arc_continuation`
- Exact Lean type: `∀ (P : ℕ) (C : GeometricCurrentOn (univ : Set (Euclid P)) 2) (Q : Submodule ℝ (Euclid P)) (z e : Euclid P) (k : ℕ) (L : ℝ), IsMinimizingIn C univ → BoundaryVanishes C → IsConeCurrent C → Module.finrank ℝ Q = 2 → z ∈ Q → e ∈ Q → ‖z‖ = 1 → ‖e‖ = 1 → inner ℝ z e = 0 → 1 ≤ k → (∃ ε : ℝ, 0 < ε ∧ C.support ∩ ball z ε = (Q : Set (Euclid P)) ∩ ball z ε ∧ ∀ y ∈ C.support, y ∈ ball z ε → HasMassDensity C y k) → (∀ φ : ℝ, 0 < φ → φ < L → Real.cos φ • z + Real.sin φ • e ∈ C.support → HasMassDensity C (Real.cos φ • z + Real.sin φ • e) k → ∃ (δ : ℝ) (k' : ℕ), 0 < δ ∧ ∀ y ∈ C.support, y ∈ ball (Real.cos φ • z + Real.sin φ • e) δ → HasMassDensity C y k') → ∀ φ : ℝ, 0 ≤ φ → φ < L → ∃ ε : ℝ, 0 < ε ∧ C.support ∩ ball (Real.cos φ • z + Real.sin φ • e) ε = (Q : Set (Euclid P)) ∩ ball (Real.cos φ • z + Real.sin φ • e) ε ∧ ∀ y ∈ C.support, y ∈ ball (Real.cos φ • z + Real.sin φ • e) ε → HasMassDensity C y k`

## Sibling prerequisites

- `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.two_dim_cone_density-a1.cone_dilation-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
