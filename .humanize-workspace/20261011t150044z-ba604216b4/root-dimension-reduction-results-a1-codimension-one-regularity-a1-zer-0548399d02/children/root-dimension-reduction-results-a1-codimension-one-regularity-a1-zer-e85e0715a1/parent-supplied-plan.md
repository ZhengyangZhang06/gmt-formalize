# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.zero_scale_limit_plane-a1.bv_compactness-a1.diagonal_subseq-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-zer-e85e0715a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.zero_scale_limit_plane-a1.bv_compactness-a1`
- Child key: `diagonal_subseq`
- Declaration: `Submission.codim1_zsl_pc_diagonal_subseq`
- Exact Lean type: `∀ (ι : Type) [Countable ι] (b : ι → ℕ → ℝ) (M : ι → ℝ), (∀ k i, |b k i| ≤ M k) → ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∀ k, ∃ L : ℝ, Tendsto (fun i => b k (σ i)) atTop (𝓝 L)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
