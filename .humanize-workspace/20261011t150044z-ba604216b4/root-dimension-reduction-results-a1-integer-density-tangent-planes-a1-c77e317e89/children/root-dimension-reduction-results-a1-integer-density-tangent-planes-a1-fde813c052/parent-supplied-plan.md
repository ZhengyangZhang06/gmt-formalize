# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_tangent_cone_planar-a1.cycle_tangent_cone-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-fde813c052/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_tangent_cone_planar-a1`
- Child key: `cycle_tangent_cone`
- Declaration: `Submission.idtp_cttp_cycle_tangent_cone`
- Exact Lean type: `∀ (P n : ℕ) (C : GeometricCurrentOn (univ : Set (Euclid P)) n), 1 ≤ n → IsMinimizingIn C univ → BoundaryVanishes C → ∀ p ∈ C.support, ∀ (lams : ℕ → ℝ) (hlams : ∀ j, 0 < lams j), Tendsto lams atTop (𝓝 0) → ∃ (φ : ℕ → ℕ) (C' : GeometricCurrentOn (univ : Set (Euclid P)) n) (θ : ℝ), StrictMono φ ∧ ConvergesWeakly (fun j => blowUp C p (lams (φ j)) (hlams (φ j)).ne') C' ∧ MassMeasuresConverge (fun j => blowUp C p (lams (φ j)) (hlams (φ j)).ne') C' ∧ IsMinimizingIn C' univ ∧ IsConeCurrent C' ∧ BoundaryVanishes C' ∧ 1 ≤ θ ∧ HasMassDensity C p θ ∧ HasMassDensity C' 0 θ`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
