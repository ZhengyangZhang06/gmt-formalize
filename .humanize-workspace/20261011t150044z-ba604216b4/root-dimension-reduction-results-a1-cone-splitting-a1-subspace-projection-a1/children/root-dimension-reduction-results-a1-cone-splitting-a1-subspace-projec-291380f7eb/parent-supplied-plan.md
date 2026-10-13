# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.cone_splitting-a1.subspace_projection-a1.current_pushforward-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-subspace-projec-291380f7eb/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.cone_splitting-a1.subspace_projection-a1`
- Child key: `current_pushforward`
- Declaration: `Submission.dimred_cs_sp_linear_pushforward`
- Exact Lean type: `∀ (P m : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid P)) m) (R : IMRep (univ : Set (Euclid P)) m) (L : Euclid P →L[ℝ] Euclid P), 0 < m → R.Represents X → IsCompact X.support → ∃ Y : GeometricCurrentOn (univ : Set (Euclid P)) m, IsIntegerMultiplicity Y ∧ Y.support ⊆ L '' X.support ∧ (BoundaryVanishes X → BoundaryVanishes Y) ∧ ∀ ω : TestFormOn (univ : Set (Euclid P)) m, Y ω = R.action (affinePullbackForm L 0 (ω : DifferentialForm (Euclid P) m))`

## Sibling prerequisites

- `root.dimension_reduction_results-a1.cone_splitting-a1.subspace_projection-a1.imrep_pushforward-a1`
- `root.density_one_implies_regular-a1.imrep_mass_and_support-a1`
- `root.density_and_tangent_cones-a1.localize-a1.imrep_current-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
