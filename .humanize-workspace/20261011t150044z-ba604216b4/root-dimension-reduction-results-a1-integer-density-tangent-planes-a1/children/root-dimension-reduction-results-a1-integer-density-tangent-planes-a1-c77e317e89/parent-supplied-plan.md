# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_tangent_cone_planar-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-c77e317e89/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1`
- Child key: `cone_tangent_cone_planar`
- Declaration: `Submission.idtp_cone_tangent_cone_planar`
- Exact Lean type: `∀ (P : ℕ) (C : GeometricCurrentOn (univ : Set (Euclid P)) 2), IsMinimizingIn C univ → BoundaryVanishes C → IsConeCurrent C → ∀ p ∈ C.support, p ≠ 0 → ∀ (lams : ℕ → ℝ) (hlams : ∀ j, 0 < lams j), Tendsto lams atTop (𝓝 0) → ∃ (φ : ℕ → ℕ) (C' : GeometricCurrentOn (univ : Set (Euclid P)) 2) (τ : Fin 2 → Euclid P) (c : ℤ), StrictMono φ ∧ ConvergesWeakly (fun j => blowUp C p (lams (φ j)) (hlams (φ j)).ne') C' ∧ MassMeasuresConverge (fun j => blowUp C p (lams (φ j)) (hlams (φ j)).ne') C' ∧ Orthonormal ℝ τ ∧ p ∈ Submodule.span ℝ (Set.range τ) ∧ 1 ≤ c.natAbs ∧ HasMassDensity C p (c.natAbs : ℝ) ∧ ∀ ω : TestFormOn (univ : Set (Euclid P)) 2, C' ω = (c : ℝ) * ∫ x in (Submodule.span ℝ (Set.range τ) : Set (Euclid P)), (ω : DifferentialForm (Euclid P) 2) x τ ∂μHE[2]`

## Sibling prerequisites

- `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.planar_constancy-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
