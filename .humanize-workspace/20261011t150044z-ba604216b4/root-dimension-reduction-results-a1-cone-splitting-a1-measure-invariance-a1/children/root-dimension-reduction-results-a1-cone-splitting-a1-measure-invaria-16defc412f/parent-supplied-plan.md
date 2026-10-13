# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.cone_splitting-a1.measure_invariance-a1.density_eq_mult-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-measure-invaria-16defc412f/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.cone_splitting-a1.measure_invariance-a1`
- Child key: `density_eq_mult`
- Declaration: `Submission.dimred_cs_mi_density_eq_mult_ae`
- Exact Lean type: `∀ (P n : ℕ) (S : GeometricCurrentOn (univ : Set (Euclid P)) n) (R : IMRep (univ : Set (Euclid P)) n) (Θ : Euclid P → ℝ), R.Represents S → (∀ x : Euclid P, HasMassDensity S x (Θ x)) → ∀ᵐ x ∂((μHE[n] : Measure (Euclid P)).restrict R.carrier), Θ x = (R.mult x : ℝ)`

## Sibling prerequisites

- `root.dimension_reduction_results-a1.cone_splitting-a1.measure_invariance-a1.density_unique-a1`
- `root.regular_set_dense-a1.density_eq_multiplicity-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
