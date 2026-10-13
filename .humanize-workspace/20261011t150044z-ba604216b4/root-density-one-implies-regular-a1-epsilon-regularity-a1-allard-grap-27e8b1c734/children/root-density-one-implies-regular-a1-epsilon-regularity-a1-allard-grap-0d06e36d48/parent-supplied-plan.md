# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.tilt_excess_step-a1.graph_area-a1.prod_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-0d06e36d48/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.tilt_excess_step-a1.graph_area-a1`
- Child key: `prod_bound`
- Declaration: `Submission.dorag_tes_ga_prod_one_add_bounds`
- Exact Lean type: `∀ (m : ℕ) (lam : Fin m → ℝ), (∀ i, 0 ≤ lam i) → (∀ i, lam i ≤ 1) → 1 ≤ ∏ i, (1 + lam i) ∧ ∏ i, (1 + lam i) ≤ 1 + 2 ^ m * ∑ i, lam i`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
