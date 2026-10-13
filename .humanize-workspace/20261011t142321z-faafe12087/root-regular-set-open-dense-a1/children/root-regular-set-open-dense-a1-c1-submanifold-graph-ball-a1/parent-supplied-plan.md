# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.regular_set_open_dense-a1.c1_submanifold_graph_ball-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-regular-set-open-dense-a1-c1-submanifold-graph-ball-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.regular_set_open_dense-a1`
- Child key: `c1_submanifold_graph_ball`
- Declaration: `Submission.rsod_isC1Submanifold_ball_inter_graph`
- Exact Lean type: `∀ (n ℓ : ℕ) (q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ) (u : Rn n → Rn ℓ) (x₀ : Amb n ℓ) (s : ℝ) (S : Set (Amb n ℓ)), 0 < s → ContDiffOn ℝ 1 u (closedBall 0 s) → (fun y => y + x₀) ⁻¹' S ∩ closedBall 0 s = q '' graphOver u (closedBall 0 s) ∩ closedBall 0 s → IsC1Submanifold n (ball x₀ s ∩ S)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
