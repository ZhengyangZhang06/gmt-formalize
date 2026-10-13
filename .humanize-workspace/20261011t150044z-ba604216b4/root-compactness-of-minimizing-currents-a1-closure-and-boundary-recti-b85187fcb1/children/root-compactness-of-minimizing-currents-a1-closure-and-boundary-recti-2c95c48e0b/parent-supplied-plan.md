# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.convergence_tools-a1.vague_subseq-a1.compact_piece-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-2c95c48e0b/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.convergence_tools-a1.vague_subseq-a1`
- Child key: `compact_piece`
- Declaration: `Submission.cbr_ct_vs_compact_piece_subseq`
- Exact Lean type: `∀ (P : ℕ) (K : Set (Euclid P)) (μs : ℕ → Measure (Euclid P)), IsCompact K → ⨆ j, μs j K < ∞ → ∃ θ : ℕ → ℕ, StrictMono θ ∧ ∀ f : Euclid P → ℝ, Continuous f → tsupport f ⊆ K → ∃ c : ℝ, Tendsto (fun j => ∫ x, f x ∂(μs (θ j))) atTop (𝓝 c)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
