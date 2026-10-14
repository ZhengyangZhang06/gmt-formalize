# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.cone_splitting-a1.subspace_projection-a1.measure_locality-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-subspace-projec-d05bfcfc45/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.cone_splitting-a1.subspace_projection-a1`
- Child key: `measure_locality`
- Declaration: `Submission.dimred_cs_sp_measure_restrict_eq_of_agree`
- Exact Lean type: `∀ (P m : ℕ) (S T : GeometricCurrentOn (univ : Set (Euclid P)) m) (RS RT : IMRep (univ : Set (Euclid P)) m) (O : Set (Euclid P)), IsOpen O → RS.Represents S → RT.Represents T → (∀ ω : TestFormOn (univ : Set (Euclid P)) m, tsupport (ω : DifferentialForm (Euclid P) m) ⊆ O → S ω = T ω) → RS.measure.restrict O = RT.measure.restrict O`

## Sibling prerequisites

- `root.density_one_implies_regular-a1.imrep_mass_and_support-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
