# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.convergence_tools-a1.vague_subseq-a1.diagonal-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-8999352df8/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.convergence_tools-a1.vague_subseq-a1`
- Child key: `diagonal`
- Declaration: `Submission.cbr_ct_vs_diagonal_subseq`
- Exact Lean type: `∀ (ι : Type) (F : ℕ → Set ι) (s : ι → ℕ → ℝ), (∀ (m : ℕ) (ψ : ℕ → ℕ), StrictMono ψ → ∃ θ : ℕ → ℕ, StrictMono θ ∧ ∀ i ∈ F m, ∃ c : ℝ, Tendsto (fun j => s i (ψ (θ j))) atTop (𝓝 c)) → ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ m : ℕ, ∀ i ∈ F m, ∃ c : ℝ, Tendsto (fun j => s i (φ j)) atTop (𝓝 c)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
