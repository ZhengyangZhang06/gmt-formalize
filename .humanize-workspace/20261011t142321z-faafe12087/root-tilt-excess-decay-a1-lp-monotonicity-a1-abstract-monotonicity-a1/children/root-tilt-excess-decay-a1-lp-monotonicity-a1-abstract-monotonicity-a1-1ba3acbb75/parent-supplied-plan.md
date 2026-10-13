# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.tilt_excess_decay-a1.lp_monotonicity-a1.abstract_monotonicity-a1.exp_perturbation_bounds-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-decay-a1-lp-monotonicity-a1-abstract-monotonicity-a1-1ba3acbb75/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.tilt_excess_decay-a1.lp_monotonicity-a1.abstract_monotonicity-a1`
- Child key: `exp_perturbation_bounds`
- Declaration: `Submission.ted_lpm_am_exp_perturbation_bounds`
- Exact Lean type: `∀ (Λ q u : ℝ), 0 < Λ → 0 ≤ q → q ≤ 1 → |u| ≤ Λ / 4 * q → Real.exp (-Λ) ≤ Real.exp u ∧ Real.exp u ≤ Real.exp Λ ∧ |Real.exp u - 1| ≤ Real.exp (Λ / 2) / 2 * Λ * q ∧ (Λ ≤ 1 → |Real.exp u - 1| ≤ Λ * q)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
