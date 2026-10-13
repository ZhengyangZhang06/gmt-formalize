# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.first_rectifiability-a1.varifold_graph_measure-a1.tangent_ball_average-a1.ball_cutoff_sandwich-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-first-rectifiability-a1-varifold-graph-measure-a1-tangent-ball-a-a8b3b6a8bb/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.first_rectifiability-a1.varifold_graph_measure-a1.tangent_ball_average-a1`
- Child key: `ball_cutoff_sandwich`
- Declaration: `Submission.frt_vgm_tba_ball_cutoff_sandwich`
- Exact Lean type: `∀ (N n : ℕ) (U : Set (Euclidean N)) (V : Varifold N n U) (x : Euclidean N) (β : C(Grassmannian N n, ℝ)) (κ t : ℝ), 0 < κ → κ < 1 → 0 < t → closedBall x (2 * t) ⊆ U → (∀ S, 0 ≤ β S) → (∫ z, max 0 (min 1 ((1 - ‖t⁻¹ • (z.1 - x)‖) / κ)) * β z.2 ∂V.measure) ≤ ∫ z in closedBall x t ×ˢ (univ : Set (Grassmannian N n)), β z.2 ∂V.measure ∧ ∫ z in closedBall x t ×ˢ (univ : Set (Grassmannian N n)), β z.2 ∂V.measure ≤ ∫ z, max 0 (min 1 ((1 + κ - ‖t⁻¹ • (z.1 - x)‖) / κ)) * β z.2 ∂V.measure`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
