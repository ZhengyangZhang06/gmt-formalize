# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_regularity-a1.open_graph_domain-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-regularity-a1-open-graph-domain-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_regularity-a1`
- Child key: `open_graph_domain`
- Declaration: `Submission.exists_open_graph_domain_of_closedBall_graph`
- Exact Lean type: `∀ {n ℓ : ℕ} (S : Set (Amb n ℓ)) (q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ) (u : Rn n → Rn ℓ) (s : ℝ), 0 < s → ContinuousOn u (closedBall 0 s) → u 0 = 0 → S ∩ closedBall 0 s = q '' graphOver u (closedBall 0 s) ∩ closedBall 0 s → ∃ W : Set (Rn n), IsOpen W ∧ (0 : Rn n) ∈ W ∧ W ⊆ ball 0 s ∧ q.symm '' S ∩ ball 0 s = graphOver u W`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
