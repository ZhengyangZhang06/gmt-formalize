# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.epsilon_regularity-a1.graph_cycle_regular-a1.approx_tangent_graph-a1.approx_tangent_le_flat-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-graph-cycle-2f14b99baf/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.graph_cycle_regular-a1.approx_tangent_graph-a1`
- Child key: `approx_tangent_le_flat`
- Declaration: `Submission.dgcr_atg_approxTangent_le_of_flat`
- Exact Lean type: `∀ (P n : ℕ) (S A : Set (Euclid P)) (x : Euclid P) (r : ℝ) (Q T : Submodule ℝ (Euclid P)), 0 < r → μHE[n] ((A ∩ ball x r) \ S) = 0 → (∀ ε : ℝ, 0 < ε → ∃ ρ : ℝ, 0 < ρ ∧ ∀ y ∈ S, dist y x < ρ → ∃ t ∈ T, ‖y - x - t‖ ≤ ε * ‖y - x‖) → HasApproximateTangentSpaceAt n A x Q → Q ≤ T`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
