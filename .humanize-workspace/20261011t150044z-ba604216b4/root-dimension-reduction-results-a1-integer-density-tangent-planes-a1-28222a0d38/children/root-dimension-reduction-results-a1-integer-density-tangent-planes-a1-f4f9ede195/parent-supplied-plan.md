# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.two_dim_cone_density-a1.density_locally_constant-a1.light_disc-a1.cone_scale_piece-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-f4f9ede195/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.two_dim_cone_density-a1.density_locally_constant-a1.light_disc-a1`
- Child key: `cone_scale_piece`
- Declaration: `Submission.idtp_tdc_dlc_ld_cone_scale_piece`
- Exact Lean type: `∀ (P : ℕ) (C : GeometricCurrentOn (univ : Set (Euclid P)) 2) (Q : Submodule ℝ (Euclid P)) (x : Euclid P) (k : ℕ) (s ε : ℝ), IsIntegerMultiplicity C → IsConeCurrent C → 0 < s → C.support ∩ ball (s⁻¹ • x) ε = (Q : Set (Euclid P)) ∩ ball (s⁻¹ • x) ε → (∀ y ∈ C.support, y ∈ ball (s⁻¹ • x) ε → HasMassDensity C y k) → C.support ∩ ball x (s * ε) = (Q : Set (Euclid P)) ∩ ball x (s * ε) ∧ ∀ y ∈ C.support, y ∈ ball x (s * ε) → HasMassDensity C y k`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
