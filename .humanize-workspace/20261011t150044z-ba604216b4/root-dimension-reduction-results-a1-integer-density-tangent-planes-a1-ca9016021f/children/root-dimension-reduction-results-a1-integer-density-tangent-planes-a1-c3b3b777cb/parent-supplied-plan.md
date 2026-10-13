# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.two_dim_cone_density-a1.density_locally_constant-a1.cone_density_function-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-c3b3b777cb/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.two_dim_cone_density-a1.density_locally_constant-a1`
- Child key: `cone_density_function`
- Declaration: `Submission.idtp_tdc_dlc_cone_density_function`
- Exact Lean type: `∀ (P : ℕ) (C : GeometricCurrentOn (univ : Set (Euclid P)) 2), IsMinimizingIn C univ → BoundaryVanishes C → IsConeCurrent C → (∃ p ∈ C.support, p ≠ 0) → ∃ Θ : Euclid P → ℝ, (∀ y : Euclid P, HasMassDensity C y (Θ y)) ∧ UpperSemicontinuous Θ ∧ (∀ q ∈ C.support, q ≠ 0 → ∃ m : ℕ, 1 ≤ m ∧ Θ q = (m : ℝ)) ∧ ∀ (s : ℝ) (x : Euclid P), 0 < s → Θ (s • x) = Θ x`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
