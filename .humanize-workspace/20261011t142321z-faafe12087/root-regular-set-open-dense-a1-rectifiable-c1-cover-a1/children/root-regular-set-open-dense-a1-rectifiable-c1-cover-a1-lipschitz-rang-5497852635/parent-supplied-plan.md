# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.regular_set_open_dense-a1.rectifiable_c1_cover-a1.lipschitz_range_c1_cover-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-regular-set-open-dense-a1-rectifiable-c1-cover-a1-lipschitz-rang-5497852635/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.regular_set_open_dense-a1.rectifiable_c1_cover-a1`
- Child key: `lipschitz_range_c1_cover`
- Declaration: `Submission.rsod_lipschitz_range_subset_c1_ranges`
- Exact Lean type: `∀ (n ℓ : ℕ) (F : Rn n → Amb n ℓ) (K : ℝ≥0), LipschitzWith K F → ∃ (N₀ : Set (Amb n ℓ)) (G : ℕ → Rn n → Amb n ℓ), (μHE[n] : Measure (Amb n ℓ)) N₀ = 0 ∧ (∀ k, ContDiff ℝ 1 (G k)) ∧ range F ⊆ N₀ ∪ ⋃ k, range (G k)`

## Sibling prerequisites

- `root.regular_set_open_dense-a1.rectifiable_c1_cover-a1.c1_approx_ball-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
