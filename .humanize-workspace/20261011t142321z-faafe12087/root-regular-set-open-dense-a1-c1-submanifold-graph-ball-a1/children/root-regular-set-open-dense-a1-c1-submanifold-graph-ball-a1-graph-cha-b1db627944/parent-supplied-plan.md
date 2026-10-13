# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.regular_set_open_dense-a1.c1_submanifold_graph_ball-a1.graph_chart_immersion-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-regular-set-open-dense-a1-c1-submanifold-graph-ball-a1-graph-cha-b1db627944/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.regular_set_open_dense-a1.c1_submanifold_graph_ball-a1`
- Child key: `graph_chart_immersion`
- Declaration: `Submission.rsod_graphChart_injective_contDiffOn_fderiv_injective`
- Exact Lean type: `∀ {n ℓ : ℕ} (q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ) (u : Rn n → Rn ℓ) (x₀ : Amb n ℓ) (Ω : Set (Rn n)), IsOpen Ω → ContDiffOn ℝ 1 u Ω → Function.Injective (fun x => q (graphPoint x (u x)) + x₀) ∧ ContDiffOn ℝ 1 (fun x => q (graphPoint x (u x)) + x₀) Ω ∧ ∀ x ∈ Ω, Function.Injective (fderiv ℝ (fun x => q (graphPoint x (u x)) + x₀) x)`

## Sibling prerequisites

- `root.regular_set_open_dense-a1.c1_submanifold_graph_ball-a1.graph_point_linear_equiv-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
