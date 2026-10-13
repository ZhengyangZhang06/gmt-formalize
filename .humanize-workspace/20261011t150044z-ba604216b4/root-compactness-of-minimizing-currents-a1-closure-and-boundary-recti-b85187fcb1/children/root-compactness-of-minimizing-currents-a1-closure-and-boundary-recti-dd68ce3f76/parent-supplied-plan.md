# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.convergence_tools-a1.vague_subseq-a1.compact_exhaustion-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-dd68ce3f76/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.convergence_tools-a1.vague_subseq-a1`
- Child key: `compact_exhaustion`
- Declaration: `Submission.cbr_ct_vs_compact_exhaustion`
- Exact Lean type: `∀ (P : ℕ) (U : Set (Euclid P)), IsOpen U → ∃ K : ℕ → Set (Euclid P), (∀ i, IsCompact (K i)) ∧ (∀ i, K i ⊆ U) ∧ ∀ C : Set (Euclid P), IsCompact C → C ⊆ U → ∃ i, C ⊆ K i`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
