# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.epsilon_regularity-a1.graph_cycle_regular-a1.boundary_weak_derivatives-a1.coordinate_covector-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-graph-cycle-5474b3f56d/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.graph_cycle_regular-a1.boundary_weak_derivatives-a1`
- Child key: `coordinate_covector`
- Declaration: `Submission.dgcr_bwd_coordinate_covector`
- Exact Lean type: `∀ (m : ℕ) (j : Fin (m + 1)), ∃ β : Covector (Euclid (m + 1)) m, ∀ i : Fin (m + 1), β (i.removeNth (fun l : Fin (m + 1) => EuclideanSpace.single l (1 : ℝ))) = if i = j then (-1 : ℝ) ^ (j : ℕ) else 0`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
