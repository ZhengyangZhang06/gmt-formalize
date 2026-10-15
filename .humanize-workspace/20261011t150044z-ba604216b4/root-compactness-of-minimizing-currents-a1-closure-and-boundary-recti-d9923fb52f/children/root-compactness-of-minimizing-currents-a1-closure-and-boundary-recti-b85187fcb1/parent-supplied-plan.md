# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.convergence_tools-a1.vague_subseq-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-b85187fcb1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.convergence_tools-a1`
- Child key: `vague_subseq`
- Declaration: `Submission.cbr_vague_convergent_subseq`
- Exact Lean type: `∀ (P : ℕ) (U : Set (Euclid P)) (μs : ℕ → Measure (Euclid P)), IsOpen U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → ⨆ j, μs j K < ∞) → ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ f : Euclid P → ℝ, Continuous f → HasCompactSupport f → tsupport f ⊆ U → ∃ c : ℝ, Tendsto (fun j => ∫ x, f x ∂(μs (φ j))) atTop (𝓝 c)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
