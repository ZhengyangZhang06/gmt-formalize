# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.first_rectifiability-a1.varifold_graph_measure-a1.measurable_plane_selection-a1.weight_closed_ball_measurable-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-first-rectifiability-a1-varifold-graph-measure-a1-measurable-pla-fed60c9267/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.first_rectifiability-a1.varifold_graph_measure-a1.measurable_plane_selection-a1`
- Child key: `weight_closed_ball_measurable`
- Declaration: `Submission.frt_vgm_mps_weight_closedBall_measurable`
- Exact Lean type: `∀ (N : ℕ) (μ : Measure (Euclidean N)), SFinite μ → ∀ r : ℝ, Measurable (fun x : Euclidean N ↦ μ (closedBall x r))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
