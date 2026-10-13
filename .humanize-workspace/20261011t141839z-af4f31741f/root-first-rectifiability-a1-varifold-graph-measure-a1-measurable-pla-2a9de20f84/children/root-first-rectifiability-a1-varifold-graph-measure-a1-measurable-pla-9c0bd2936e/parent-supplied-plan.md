# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.first_rectifiability-a1.varifold_graph_measure-a1.measurable_plane_selection-a1.grassmannian_limit_selection-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-first-rectifiability-a1-varifold-graph-measure-a1-measurable-pla-9c0bd2936e/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.first_rectifiability-a1.varifold_graph_measure-a1.measurable_plane_selection-a1`
- Child key: `grassmannian_limit_selection`
- Declaration: `Submission.frt_vgm_mps_limit_selection`
- Exact Lean type: `∀ (X : Type) [MeasurableSpace X] (N n : ℕ), Nonempty (Grassmannian N n) → ∀ (a : ℕ → X → Fin N → Fin N → ℝ), (∀ (k : ℕ) (i j : Fin N), Measurable (fun x ↦ a k x i j)) → ∃ τ : X → Grassmannian N n, Measurable τ ∧ ∀ (x : X) (T : Grassmannian N n), (∀ i j : Fin N, Tendsto (fun k ↦ a k x i j) atTop (𝓝 (T.1 i j))) → τ x = T`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
