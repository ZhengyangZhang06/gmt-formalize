# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.first_rectifiability-a1.varifold_graph_measure-a1.measurable_plane_selection-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-first-rectifiability-a1-varifold-graph-measure-a1-measurable-pla-2a9de20f84/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.first_rectifiability-a1.varifold_graph_measure-a1`
- Child key: `measurable_plane_selection`
- Declaration: `Submission.frt_vgm_measurable_plane_selection`
- Exact Lean type: `∀ (N n : ℕ) (U : Set (Euclidean N)) (V : Varifold N n U), Nonempty (Grassmannian N n) → ∃ τ : Euclidean N → Grassmannian N n, Measurable τ ∧ ∀ (x : Euclidean N) (T : Grassmannian N n), (∀ β : C(Grassmannian N n, ℝ), Tendsto (fun ρ : ℝ ↦ (∫ z in closedBall x ρ ×ˢ (univ : Set (Grassmannian N n)), β z.2 ∂V.measure) / (V.weight (closedBall x ρ)).toReal) (𝓝[>] 0) (𝓝 (β T))) → τ x = T`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
