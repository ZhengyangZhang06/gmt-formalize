# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.offvertex_rep-a1.vertex_negligible-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-sim-41602e5705/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.offvertex_rep-a1`
- Child key: `vertex_negligible`
- Declaration: `Submission.codim1_ovr_imrep_vanish_at_vertex`
- Exact Lean type: `∀ (P m : ℕ) (C : GeometricCurrentOn (univ : Set (Euclid P)) m) (ωs : ℕ → TestFormOn (univ : Set (Euclid P)) m) (r : ℕ → ℝ) (c : ℝ), 1 ≤ m → IsIntegerMultiplicity C → Tendsto r atTop (𝓝 0) → (∀ (k : ℕ) (x : Euclid P), r k ≤ ‖x‖ → (ωs k : DifferentialForm (Euclid P) m) x = 0) → (∀ (k : ℕ) (x : Euclid P), covectorEuclideanNorm ((ωs k : DifferentialForm (Euclid P) m) x) ≤ c) → Tendsto (fun k => C (ωs k)) atTop (𝓝 0)`

## Sibling prerequisites

- `root.density_one_implies_regular-a1.imrep_mass_and_support-a1.unit_orientation_duality-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
