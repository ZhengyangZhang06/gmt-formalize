# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.tilt_excess_decay-a1.lp_monotonicity-a1.abstract_monotonicity-a1.cutoff_sequence-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-decay-a1-lp-monotonicity-a1-abstract-monotonicity-a1-24b9e1810f/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.tilt_excess_decay-a1.lp_monotonicity-a1.abstract_monotonicity-a1`
- Child key: `cutoff_sequence`
- Declaration: `Submission.ted_lpm_am_cutoff_sequence`
- Exact Lean type: `∀ ε₁ : ℝ, 0 < ε₁ → ∃ (φ : ℕ → ℝ → ℝ) (ε : ℕ → ℝ), (∀ k, 0 < ε k ∧ ε k ≤ ε₁) ∧ Tendsto ε atTop (𝓝 0) ∧ (∀ k, ContDiff ℝ 1 (φ k)) ∧ (∀ k, Antitone (φ k)) ∧ (∀ k s, 0 ≤ φ k s ∧ φ k s ≤ 1) ∧ (∀ k s, s ≤ 1 → φ k s = 1) ∧ (∀ k s, 1 + ε k ≤ s → φ k s = 0) ∧ (∀ s, 1 < s → ∀ᶠ k in atTop, φ k s = 0)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
