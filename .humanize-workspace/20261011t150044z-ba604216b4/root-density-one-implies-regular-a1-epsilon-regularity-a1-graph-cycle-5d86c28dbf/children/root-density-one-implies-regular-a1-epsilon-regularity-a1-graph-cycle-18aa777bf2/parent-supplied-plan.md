# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.epsilon_regularity-a1.graph_cycle_regular-a1.boundary_weak_derivatives-a1.extderiv_smul_const-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-graph-cycle-18aa777bf2/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.graph_cycle_regular-a1.boundary_weak_derivatives-a1`
- Child key: `extderiv_smul_const`
- Declaration: `Submission.dgcr_bwd_extDeriv_smul_const`
- Exact Lean type: `∀ (P m : ℕ) (a : Euclid P → ℝ) (β : Covector (Euclid P) m) (x : Euclid P) (w : Fin (m + 1) → Euclid P), DifferentiableAt ℝ a x → exteriorDerivative (fun y => a y • β) x w = ∑ i : Fin (m + 1), (-1 : ℝ) ^ (i : ℕ) * (fderiv ℝ a x (w i) * β (i.removeNth w))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
