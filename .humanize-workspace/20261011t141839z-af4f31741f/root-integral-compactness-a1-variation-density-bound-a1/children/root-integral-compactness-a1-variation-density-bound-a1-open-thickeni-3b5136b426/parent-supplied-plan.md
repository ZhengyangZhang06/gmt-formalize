# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.integral_compactness-a1.variation_density_bound-a1.open_thickening_exhaustion-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-integral-compactness-a1-variation-density-bound-a1-open-thickeni-3b5136b426/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.integral_compactness-a1.variation_density_bound-a1`
- Child key: `open_thickening_exhaustion`
- Declaration: `Submission.intcpt_vdb_open_thickening_exhaustion`
- Exact Lean type: `∀ (N : ℕ) (U : Set (Euclidean N)), IsOpen U → ∃ (W : ℕ → Set (Euclidean N)) (r : ℕ → ℝ), (∀ p, 0 < r p) ∧ (∀ p, IsRelCompactOpenIn (thickening (r p) (W p)) U) ∧ U ⊆ ⋃ p, W p`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
