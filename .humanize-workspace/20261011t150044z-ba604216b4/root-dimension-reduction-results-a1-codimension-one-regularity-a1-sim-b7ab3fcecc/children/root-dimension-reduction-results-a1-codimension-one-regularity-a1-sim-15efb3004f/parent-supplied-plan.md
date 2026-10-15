# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.offvertex_rep-a1.vertex_extension-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-sim-15efb3004f/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.offvertex_rep-a1`
- Child key: `vertex_extension`
- Declaration: `Submission.codim1_ovr_extend_rep_across_vertex`
- Exact Lean type: `∀ (P m : ℕ) (C : GeometricCurrentOn (univ : Set (Euclid P)) m) (M : Set (Euclid P)) (ξ : Euclid P → MultiVector P m), 1 ≤ m → IsIntegerMultiplicity C → MeasurableSet M → (0 : Euclid P) ∉ M → ContinuousOn ξ M → (∀ x ∈ M, ∀ α : Covector (Euclid P) m, |ξ x α| ≤ covectorEuclideanNorm α) → (∀ K : Set (Euclid P), IsCompact K → μHE[m] (M ∩ K) ≠ ∞) → (∀ ω : TestFormOn (univ : Set (Euclid P)) m, (0 : Euclid P) ∉ tsupport (ω : DifferentialForm (Euclid P) m) → C ω = ∫ x in M, ξ x ((ω : DifferentialForm (Euclid P) m) x) ∂μHE[m]) → ∀ ω : TestFormOn (univ : Set (Euclid P)) m, C ω = ∫ x in M, ξ x ((ω : DifferentialForm (Euclid P) m) x) ∂μHE[m]`

## Sibling prerequisites

- `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.offvertex_rep-a1.vertex_negligible-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
