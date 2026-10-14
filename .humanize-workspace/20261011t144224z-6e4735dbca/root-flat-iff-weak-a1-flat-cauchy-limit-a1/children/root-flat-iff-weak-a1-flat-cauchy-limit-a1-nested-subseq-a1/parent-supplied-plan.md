# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.flat_iff_weak-a1.flat_cauchy_limit-a1.nested_subseq-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-flat-iff-weak-a1-flat-cauchy-limit-a1-nested-subseq-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.flat_iff_weak-a1.flat_cauchy_limit-a1`
- Child key: `nested_subseq`
- Declaration: `Submission.fiw_fcl_nested_subseq`
- Exact Lean type: `∀ (Q : ℕ → ℕ → ℕ → Prop), (∀ r : ℕ, ∀ J : Set ℕ, J.Infinite → ∃ J' ⊆ J, J'.Infinite ∧ ∀ i ∈ J', ∀ j ∈ J', Q r i j) → ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ r : ℕ, Q r (φ r) (φ (r + 1))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
