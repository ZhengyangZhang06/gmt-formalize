# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.allard_regularity-a1.density_bounds-a1.annular_monotonicity-a1.fixed_cutoff-a1.cutoff_facts-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-regularity-a1-density-bounds-a1-annular-monotonicity-a1-f-d2493da3c8/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.allard_regularity-a1.density_bounds-a1.annular_monotonicity-a1.fixed_cutoff-a1`
- Child key: `cutoff_facts`
- Declaration: `Submission.allard52_am_fc_cutoff_facts`
- Exact Lean type: `∀ (φ : ℝ → ℝ) (ε : ℝ), 0 < ε → ContDiff ℝ 1 φ → Antitone φ → (∀ u : ℝ, u ≤ 1 → φ u = 1) → (∀ u : ℝ, 1 + ε ≤ u → φ u = 0) → (∀ u : ℝ, 0 ≤ φ u ∧ φ u ≤ 1) ∧ (∀ u : ℝ, deriv φ u ≤ 0) ∧ (∀ u : ℝ, 1 + ε < u → deriv φ u = 0) ∧ Continuous (deriv φ) ∧ ∃ C : ℝ, ∀ u : ℝ, |deriv φ u| ≤ C`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
