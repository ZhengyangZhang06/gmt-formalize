# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.density_one_local_rep-a1.rep_support-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-sim-e5b05df4fc/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.density_one_local_rep-a1`
- Child key: `rep_support`
- Declaration: `Submission.codim1_dolr_rep_support_inter`
- Exact Lean type: `∀ (P m : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U m) (W M : Set (Euclid P)) (k : ℤ) (ξ : Euclid P → MultiVector P m), IsOpen W → W ⊆ U → k ≠ 0 → IsEmbeddedSubmanifold 1 m M → IsOrientation m M ξ → closure M ∩ W ⊆ M → (∀ K : Set (Euclid P), IsCompact K → K ⊆ W → μHE[m] (M ∩ K) ≠ ∞) → (∀ ω : TestFormOn U m, tsupport (ω : DifferentialForm (Euclid P) m) ⊆ W → T ω = k * ∫ x in M, ξ x ((ω : DifferentialForm (Euclid P) m) x) ∂μHE[m]) → T.support ∩ W = M ∩ W`

## Sibling prerequisites

- `root.dimension_reduction_results-a1.regular_point_density-a1.locally_closed-a1`
- `root.dimension_reduction_results-a1.regular_point_density-a1.density_one-a1`
- `root.dimension_reduction_results-a1.regular_point_density-a1.mass_identity-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
