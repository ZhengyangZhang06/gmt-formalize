# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.lipschitz_pushforward-a1.existence-a1.index_cauchy-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-onto-skeleton-a1-pushforward-homotopy-a1-lipschit-23fd0e85aa/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.lipschitz_pushforward-a1.existence-a1`
- Child key: `index_cauchy`
- Declaration: `Submission.dph_lpfex_tendsto_of_index_maps`
- Exact Lean type: `∀ a : ℕ → ℝ, (∀ p q : ℕ → ℕ, Tendsto p atTop atTop → Tendsto q atTop atTop → Tendsto (fun i => a (q i) - a (p i)) atTop (𝓝 0)) → ∃ s : ℝ, Tendsto a atTop (𝓝 s)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
