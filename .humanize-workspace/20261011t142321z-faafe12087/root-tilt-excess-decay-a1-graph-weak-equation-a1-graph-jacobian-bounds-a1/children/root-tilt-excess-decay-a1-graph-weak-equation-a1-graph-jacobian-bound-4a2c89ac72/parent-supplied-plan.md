# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.tilt_excess_decay-a1.graph_weak_equation-a1.graph_jacobian_bounds-a1.det_one_add_bounds-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-decay-a1-graph-weak-equation-a1-graph-jacobian-bound-4a2c89ac72/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.tilt_excess_decay-a1.graph_weak_equation-a1.graph_jacobian_bounds-a1`
- Child key: `det_one_add_bounds`
- Declaration: `Submission.gwe_gjb_det_one_add_bounds`
- Exact Lean type: `∀ (n : ℕ) (G : Matrix (Fin n) (Fin n) ℝ), Matrix.IsSymm G → (∀ x : Fin n → ℝ, 0 ≤ dotProduct x (Matrix.mulVec G x)) → 1 ≤ Matrix.det ((1 : Matrix (Fin n) (Fin n) ℝ) + G) ∧ Matrix.det ((1 : Matrix (Fin n) (Fin n) ℝ) + G) ≤ Real.exp (Matrix.trace G)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
