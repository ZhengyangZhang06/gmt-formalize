# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.cone_filling_subspace-a1.cone_current-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-split-off-spine-77a7f533dd/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.cone_filling_subspace-a1`
- Child key: `cone_current`
- Declaration: `Submission.dimred_cs_sos_cfs_cone_current`
- Exact Lean type: `∀ (P q : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid P)) (q + 1)) (R : IMRep (univ : Set (Euclid P)) (q + 1)), R.Represents X → R.carrier ⊆ X.support → R.measure univ ≠ ∞ → X.boundary = 0 → IsCompact X.support → ∃ Y : GeometricCurrentOn (univ : Set (Euclid P)) (q + 1 + 1), Y.boundary = X ∧ IsCompact Y.support ∧ Y.support ⊆ {y : Euclid P | ∃ s ∈ Icc (0 : ℝ) 1, ∃ x ∈ X.support, y = s • x} ∧ ∀ ω : TestFormOn (univ : Set (Euclid P)) (q + 1 + 1), ∃ η : TestFormOn (univ : Set (Euclid P)) (q + 1), (∀ x ∈ X.support, (η : DifferentialForm (Euclid P) (q + 1)) x = ∫ t in (0 : ℝ)..1, t ^ (q + 1) • ((ω : DifferentialForm (Euclid P) (q + 1 + 1)) (t • x)).curryLeft x) ∧ Y ω = X η`

## Sibling prerequisites

- `root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.cone_filling_subspace-a1.radial_homotopy-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
