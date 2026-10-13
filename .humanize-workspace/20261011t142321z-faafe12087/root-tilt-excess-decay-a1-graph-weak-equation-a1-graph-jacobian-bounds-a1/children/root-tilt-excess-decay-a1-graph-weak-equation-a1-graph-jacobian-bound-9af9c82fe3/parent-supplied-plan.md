# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.tilt_excess_decay-a1.graph_weak_equation-a1.graph_jacobian_bounds-a1.exp_half_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-decay-a1-graph-weak-equation-a1-graph-jacobian-bound-9af9c82fe3/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.tilt_excess_decay-a1.graph_weak_equation-a1.graph_jacobian_bounds-a1`
- Child key: `exp_half_bound`
- Declaration: `Submission.gwe_gjb_exp_half_le`
- Exact Lean type: `∀ (s T : ℝ), 0 ≤ s → s ≤ T → Real.exp (s / 2) ≤ 1 + Real.exp (T / 2) / 2 * s`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
