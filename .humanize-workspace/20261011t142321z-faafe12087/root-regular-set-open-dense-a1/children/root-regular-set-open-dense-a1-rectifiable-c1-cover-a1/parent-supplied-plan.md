# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.regular_set_open_dense-a1.rectifiable_c1_cover-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-regular-set-open-dense-a1-rectifiable-c1-cover-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.regular_set_open_dense-a1`
- Child key: `rectifiable_c1_cover`
- Declaration: `Submission.rsod_rectifiable_subset_c1_cover`
- Exact Lean type: `∀ (n ℓ : ℕ), 1 ≤ n → ∀ (M : Set (Amb n ℓ)), Poincare.SimonGMT.Chapter03.CountablyRectifiable n M → ∃ (N₀ : Set (Amb n ℓ)) (N : ℕ → Set (Amb n ℓ)), (μHE[n] : Measure (Amb n ℓ)) N₀ = 0 ∧ (∀ j, IsC1Submanifold n (N j) ∧ (μHE[n] : Measure (Amb n ℓ)) (N j) < ∞) ∧ M ⊆ N₀ ∪ ⋃ j, N j`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
