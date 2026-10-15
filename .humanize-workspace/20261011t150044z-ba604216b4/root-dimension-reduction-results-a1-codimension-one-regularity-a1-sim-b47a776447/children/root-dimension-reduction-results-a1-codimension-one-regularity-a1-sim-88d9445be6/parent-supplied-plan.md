# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.density_one_local_rep-a1.rep_density-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-sim-88d9445be6/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.density_one_local_rep-a1`
- Child key: `rep_density`
- Declaration: `Submission.codim1_dolr_rep_hasMassDensity`
- Exact Lean type: `∀ (P m : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U m) (y : Euclid P) (ρ : ℝ) (k : ℤ) (M : Set (Euclid P)) (ξ : Euclid P → MultiVector P m), 0 < ρ → ball y ρ ⊆ U → y ∈ M → IsEmbeddedSubmanifold 1 m M → IsOrientation m M ξ → (∀ K : Set (Euclid P), IsCompact K → K ⊆ ball y ρ → μHE[m] (M ∩ K) ≠ ∞) → (∀ ω : TestFormOn U m, tsupport (ω : DifferentialForm (Euclid P) m) ⊆ ball y ρ → T ω = k * ∫ x in M, ξ x ((ω : DifferentialForm (Euclid P) m) x) ∂μHE[m]) → HasMassDensity T y (k.natAbs : ℝ)`

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
