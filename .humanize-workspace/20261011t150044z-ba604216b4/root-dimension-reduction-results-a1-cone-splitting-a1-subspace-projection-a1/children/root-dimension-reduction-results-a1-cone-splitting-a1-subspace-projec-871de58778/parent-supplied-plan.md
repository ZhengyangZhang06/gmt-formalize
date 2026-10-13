# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.cone_splitting-a1.subspace_projection-a1.imrep_pushforward-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-subspace-projec-871de58778/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.cone_splitting-a1.subspace_projection-a1`
- Child key: `imrep_pushforward`
- Declaration: `Submission.dimred_cs_sp_imrep_linear_pushforward`
- Exact Lean type: `∀ (P m : ℕ) (R : IMRep (univ : Set (Euclid P)) m) (L : Euclid P →L[ℝ] Euclid P) (K : Set (Euclid P)), 0 < m → IsCompact K → R.measure Kᶜ = 0 → ∃ R' : IMRep (univ : Set (Euclid P)) m, R'.carrier ⊆ L '' K ∧ ∀ ω : TestFormOn (univ : Set (Euclid P)) m, R'.action (ω : DifferentialForm (Euclid P) m) = R.action (affinePullbackForm L 0 (ω : DifferentialForm (Euclid P) m))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
