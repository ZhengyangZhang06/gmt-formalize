# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.offvertex_rep-a1.partition_glue-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-sim-7f4f3585f5/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.offvertex_rep-a1`
- Child key: `partition_glue`
- Declaration: `Submission.codim1_ovr_partition_glue_rep`
- Exact Lean type: `∀ (P m : ℕ) (C : GeometricCurrentOn (univ : Set (Euclid P)) m) (M O : Set (Euclid P)) (ξ : Euclid P → MultiVector P m), IsOpen O → MeasurableSet M → ContinuousOn ξ M → (∀ x ∈ M, ∀ α : Covector (Euclid P) m, |ξ x α| ≤ covectorEuclideanNorm α) → (∀ K : Set (Euclid P), IsCompact K → μHE[m] (M ∩ K) ≠ ∞) → (∀ x ∈ O, ∃ B : Set (Euclid P), IsOpen B ∧ x ∈ B ∧ ∀ ω : TestFormOn (univ : Set (Euclid P)) m, tsupport (ω : DifferentialForm (Euclid P) m) ⊆ B → C ω = ∫ z in M, ξ z ((ω : DifferentialForm (Euclid P) m) z) ∂μHE[m]) → ∀ ω : TestFormOn (univ : Set (Euclid P)) m, tsupport (ω : DifferentialForm (Euclid P) m) ⊆ O → C ω = ∫ z in M, ξ z ((ω : DifferentialForm (Euclid P) m) z) ∂μHE[m]`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
