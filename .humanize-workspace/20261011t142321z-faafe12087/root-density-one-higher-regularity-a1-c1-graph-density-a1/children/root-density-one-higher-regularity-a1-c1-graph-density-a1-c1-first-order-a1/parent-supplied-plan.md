# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_higher_regularity-a1.c1_graph_density-a1.c1_first_order-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-higher-regularity-a1-c1-graph-density-a1-c1-first-order-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_higher_regularity-a1.c1_graph_density-a1`
- Child key: `c1_first_order`
- Declaration: `Submission.dohr_c1_uniform_first_order`
- Exact Lean type: `∀ (n ℓ : ℕ) (U : Set (Rn n)) (u : Rn n → Rn ℓ), IsOpen U → ContDiffOn ℝ 1 u U → ∀ x₀ ∈ U, ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧ closedBall x₀ η ⊆ U ∧ ∀ x ∈ closedBall x₀ η, ∀ y ∈ closedBall x₀ η, ‖u x - u y - fderiv ℝ u x₀ (x - y)‖ ≤ ε * ‖x - y‖`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
