# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.cone_splitting-a1.translation_invariance-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-translation-invariance-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.cone_splitting-a1`
- Child key: `translation_invariance`
- Declaration: `Submission.dimred_cs_translation_invariant_of_tangency`
- Exact Lean type: `∀ (P n : ℕ) (S : GeometricCurrentOn (univ : Set (Euclid P)) n) (R : IMRep (univ : Set (Euclid P)) n) (v : Euclid P), 0 < n → R.Represents S → BoundaryVanishes S → (∀ᵐ x ∂R.measure, (approxTangentPlane n R.carrier x).starProjection v = v) → ∀ ω : TestFormOn (univ : Set (Euclid P)) n, currentEval (blowUp S (-v) 1 one_ne_zero) (ω : DifferentialForm (Euclid P) n) = S ω`

## Sibling prerequisites

- `root.half_space_cone_lies_in_boundary-a1.imrep_measure_unique-a1.orientation_norm_bound-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
