# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.radon_compactness-a1.rc_diagonal_subseq-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/nodes/root-radon-compactness-a1-rc-diagonal-subseq-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.radon_compactness-a1`
- Child key: `rc_diagonal_subseq`
- Declaration: `Submission.rc_diagonal_subseq`
- Exact Lean type: `∀ (ι : Type u) [Countable ι] (a : ℕ → ι → ℝ), (∀ i, ∃ C : ℝ, ∀ k, |a k i| ≤ C) → ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ i, ∃ l : ℝ, Tendsto (fun k => a (φ k) i) atTop (𝓝 l)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
