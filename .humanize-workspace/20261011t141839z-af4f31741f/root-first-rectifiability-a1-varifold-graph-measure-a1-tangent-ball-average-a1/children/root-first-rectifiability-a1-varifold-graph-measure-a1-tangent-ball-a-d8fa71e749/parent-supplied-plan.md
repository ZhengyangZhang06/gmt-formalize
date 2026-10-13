# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.first_rectifiability-a1.varifold_graph_measure-a1.tangent_ball_average-a1.plane_cutoff_bounds-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-first-rectifiability-a1-varifold-graph-measure-a1-tangent-ball-a-d8fa71e749/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.first_rectifiability-a1.varifold_graph_measure-a1.tangent_ball_average-a1`
- Child key: `plane_cutoff_bounds`
- Declaration: `Submission.frt_vgm_tba_plane_cutoff_bounds`
- Exact Lean type: `∀ (N n : ℕ) (T : Grassmannian N n) (κ : ℝ), 0 < κ → κ < 1 → (unitBallVolume n).toReal * (1 - κ) ^ n ≤ ∫ y in (T.plane : Set (Euclidean N)), max 0 (min 1 ((1 - ‖y‖) / κ)) ∂μHE[n] ∧ ∫ y in (T.plane : Set (Euclidean N)), max 0 (min 1 ((1 + κ - ‖y‖) / κ)) ∂μHE[n] ≤ (unitBallVolume n).toReal * (1 + κ) ^ n`

## Sibling prerequisites

- `root.first_rectifiability-a1.varifold_graph_measure-a1.tangent_ball_average-a1.plane_ball-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
