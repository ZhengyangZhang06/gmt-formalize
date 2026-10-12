# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.first_rectifiability-a1.varifold_graph_measure-a1.measurable_plane_selection-a1.ball_integral_measurable-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-first-rectifiability-a1-varifold-graph-measure-a1-measurable-pla-7b6c1c4c4a/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.first_rectifiability-a1.varifold_graph_measure-a1.measurable_plane_selection-a1`
- Child key: `ball_integral_measurable`
- Declaration: `Submission.frt_vgm_mps_ball_integral_measurable`
- Exact Lean type: `∀ (N n : ℕ) (ν : Measure (Euclidean N × Grassmannian N n)), SFinite ν → ∀ (r : ℝ) (β : C(Grassmannian N n, ℝ)), Measurable (fun x : Euclidean N ↦ ∫ z in closedBall x r ×ˢ (univ : Set (Grassmannian N n)), β z.2 ∂ν)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
