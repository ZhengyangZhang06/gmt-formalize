# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.flat_convergence-a1.cauchy_subseq-a1.diagonal_subseq-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-flat-convergence-a1-cauchy-81bbc80940/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.flat_convergence-a1.cauchy_subseq-a1`
- Child key: `diagonal_subseq`
- Declaration: `Submission.cmc_fc_cs_diagonal_subseq`
- Exact Lean type: `∀ (C : ℕ → ℕ → ℕ → Prop), (∀ (r : ℕ) (I : Set ℕ), I.Infinite → ∃ J ⊆ I, J.Infinite ∧ ∀ j ∈ J, ∀ l ∈ J, C r j l) → ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ r, C r (φ (r + 1)) (φ r)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
