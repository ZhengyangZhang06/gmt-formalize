# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_higher_regularity-a1.euler_lagrange-a1.graph_fderiv-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-higher-regularity-a1-euler-lagrange-a1-graph-fderiv-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_higher_regularity-a1.euler_lagrange-a1`
- Child key: `graph_fderiv`
- Declaration: `Submission.dohr_vel_graph_fderiv`
- Exact Lean type: `∀ n ℓ : ℕ, ∀ (u : Rn n → Rn ℓ) (x : Rn n), DifferentiableAt ℝ u x → DifferentiableAt ℝ (fun z : Rn n => graphPoint z (u z)) x ∧ ∀ v : Rn n, fderiv ℝ (fun z : Rn n => graphPoint z (u z)) x v = graphPoint v (fderiv ℝ u x v)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
