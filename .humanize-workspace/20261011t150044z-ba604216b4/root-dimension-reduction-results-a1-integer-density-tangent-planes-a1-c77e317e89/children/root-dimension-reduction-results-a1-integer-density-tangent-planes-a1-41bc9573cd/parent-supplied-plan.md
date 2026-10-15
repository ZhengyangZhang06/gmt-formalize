# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_tangent_cone_planar-a1.planar_support_splitting-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-41bc9573cd/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_tangent_cone_planar-a1`
- Child key: `planar_support_splitting`
- Declaration: `Submission.idtp_cttp_planar_support`
- Exact Lean type: `∀ (P : ℕ) (S : GeometricCurrentOn (univ : Set (Euclid P)) 2) (p : Euclid P) (θ : ℝ), p ≠ 0 → IsMinimizingIn S univ → BoundaryVanishes S → (∀ y ∈ Submodule.span ℝ {p}, ∀ lam : ℝ, 0 < lam → ∀ (w : Euclid P) (θ' : ℝ), HasMassDensity S w θ' → HasMassDensity S (y + lam • w) θ') → 1 ≤ θ → HasMassDensity S 0 θ → ∃ τ : Fin 2 → Euclid P, Orthonormal ℝ τ ∧ p ∈ Submodule.span ℝ (Set.range τ) ∧ S.support ⊆ (Submodule.span ℝ (Set.range τ) : Set (Euclid P))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
