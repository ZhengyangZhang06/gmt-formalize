# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.tilt_excess_decay-a1.graph_weak_equation-a1.graph_tilt_algebra-a1.proj_inner_defect-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-decay-a1-graph-weak-equation-a1-graph-tilt-algebra-a-56631c5d1c/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.tilt_excess_decay-a1.graph_weak_equation-a1.graph_tilt_algebra-a1`
- Child key: `proj_inner_defect`
- Declaration: `Submission.gwe_gta_proj_inner_defect`
- Exact Lean type: `∀ (m : ℕ) (S T : Submodule ℝ (Rn m)) (u w : Rn m), u ∈ T → w ∈ T → |inner ℝ (S.starProjection u) (S.starProjection w) - inner ℝ u w| ≤ hsNormSq (S.starProjection - T.starProjection) * (‖u‖ * ‖w‖)`

## Sibling prerequisites

- `root.tilt_excess_height_estimate-a1.projection_algebra-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
