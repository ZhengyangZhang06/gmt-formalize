# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.planar_constancy-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-77d7be4677/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1`
- Child key: `planar_constancy`
- Declaration: `Submission.idtp_planar_cycle_eq_const_mul`
- Exact Lean type: `∀ (P n : ℕ) (V : Set (Euclid P)) (S : GeometricCurrentOn V n) (τ : Fin n → Euclid P), 1 ≤ n → IsOpen V → Orthonormal ℝ τ → IsIntegerMultiplicity S → BoundaryVanishes S → S.support ⊆ (Submodule.span ℝ (Set.range τ) : Set (Euclid P)) → IsConnected (V ∩ (Submodule.span ℝ (Set.range τ) : Set (Euclid P))) → ∃ c : ℤ, (∀ ω : TestFormOn V n, S ω = (c : ℝ) * ∫ x in V ∩ (Submodule.span ℝ (Set.range τ) : Set (Euclid P)), (ω : DifferentialForm (Euclid P) n) x τ ∂μHE[n]) ∧ ∀ W : Set (Euclid P), IsOpen W → W ⊆ V → S.massOn W = (c.natAbs : ℝ≥0∞) * μHE[n] (W ∩ (Submodule.span ℝ (Set.range τ) : Set (Euclid P)))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
