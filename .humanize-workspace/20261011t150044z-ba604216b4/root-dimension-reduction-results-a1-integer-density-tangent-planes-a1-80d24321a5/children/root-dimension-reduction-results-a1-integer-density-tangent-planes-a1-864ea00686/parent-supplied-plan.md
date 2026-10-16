# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.integer_density-a1.spine_density_integer-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-864ea00686/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.integer_density-a1`
- Child key: `spine_density_integer`
- Declaration: `Submission.idod_spine_invariant_density_nat`
- Exact Lean type: `∀ (P n : ℕ) (S : GeometricCurrentOn (univ : Set (Euclid P)) n) (L : Submodule ℝ (Euclid P)) (θ₀ : ℝ), Module.finrank ℝ L < n → n ≤ Module.finrank ℝ L + 2 → IsMinimizingIn S univ → BoundaryVanishes S → (∀ y ∈ L, ∀ lam : ℝ, 0 < lam → ∀ (w : Euclid P) (θ : ℝ), HasMassDensity S w θ → HasMassDensity S (y + lam • w) θ) → HasMassDensity S 0 θ₀ → ∃ m : ℕ, θ₀ = m`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
