# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.monotonicity-a1.smoothed_bounds-a1.profile-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-7bce5c34b9/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.monotonicity-a1.smoothed_bounds-a1`
- Child key: `profile`
- Declaration: `Submission.doragm_sab_cutoff_profile`
- Exact Lean type: `∀ (A : ℝ), 1 < A → ∃ φ : ℝ → ℝ, ContDiff ℝ 1 φ ∧ Antitone φ ∧ (∀ u, 0 ≤ φ u ∧ φ u ≤ 1) ∧ (∀ u, u ≤ 1 → φ u = 1) ∧ (∀ u, A ≤ u → φ u = 0) ∧ (∀ u, deriv φ u ≤ 0) ∧ (∀ u, deriv φ u ≠ 0 → 1 < u ∧ u < A)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
