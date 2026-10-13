# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.allard_regularity-a1.density_bounds-a1.annular_monotonicity-a1.cutoff_limit-a1.cutoff_sequence-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-regularity-a1-density-bounds-a1-annular-monotonicity-a1-c-107d5370b3/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.allard_regularity-a1.density_bounds-a1.annular_monotonicity-a1.cutoff_limit-a1`
- Child key: `cutoff_sequence`
- Declaration: `Submission.allard52_amcl_cutoff_sequence`
- Exact Lean type: `∃ (φ : ℕ → ℝ → ℝ) (ε : ℕ → ℝ), (∀ k, 0 < ε k ∧ ε k ≤ 1) ∧ Tendsto ε atTop (𝓝 0) ∧ (∀ k, ContDiff ℝ 1 (φ k)) ∧ (∀ k, Antitone (φ k)) ∧ (∀ k u, 0 ≤ φ k u ∧ φ k u ≤ 1) ∧ (∀ k u, u ≤ 1 → φ k u = 1) ∧ (∀ k u, 1 + ε k ≤ u → φ k u = 0)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
