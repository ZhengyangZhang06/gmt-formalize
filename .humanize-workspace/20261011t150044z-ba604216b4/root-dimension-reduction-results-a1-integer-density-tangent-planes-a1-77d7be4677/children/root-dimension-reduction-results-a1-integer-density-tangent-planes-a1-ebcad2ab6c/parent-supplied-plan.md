# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.planar_constancy-a1.boundary_weak_derivative-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-ebcad2ab6c/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.planar_constancy-a1`
- Child key: `boundary_weak_derivative`
- Declaration: `Submission.idtp_pc_boundary_weak_derivative`
- Exact Lean type: `∀ (P n : ℕ) (V : Set (Euclid P)) (S : GeometricCurrentOn V n) (τ : Fin n → Euclid P) (g : Euclid P → ℝ), 1 ≤ n → Orthonormal ℝ τ → BoundaryVanishes S → (∀ ω : TestFormOn V n, S ω = ∫ x in V ∩ (Submodule.span ℝ (Set.range τ) : Set (Euclid P)), g x * (ω : DifferentialForm (Euclid P) n) x τ ∂μHE[n]) → ∀ f : Euclid P → ℝ, ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f → tsupport f ⊆ V → ∀ j : Fin n, ∫ x in V ∩ (Submodule.span ℝ (Set.range τ) : Set (Euclid P)), g x * fderiv ℝ f x (τ j) ∂μHE[n] = 0`

## Sibling prerequisites

- `root.density_one_implies_regular-a1.epsilon_regularity-a1.graph_cycle_regular-a1.boundary_weak_derivatives-a1.coordinate_covector-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
