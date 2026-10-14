# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.weight_ge_one-a1.plane_map-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-dc6dd1f809/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.weight_ge_one-a1`
- Child key: `plane_map`
- Declaration: `Submission.cbr_ci_pw_plane_map_volume`
- Exact Lean type: `∀ (P n : ℕ) (v : Fin n → Euclid P) (w : Euclid P) (pL : Euclid P →L[ℝ] Euclid n), Orthonormal ℝ v → (∀ (x : Euclid P) (i : Fin n), pL x i = inner ℝ (v i) x) → Measure.map pL ((μHE[n]).restrict {y : Euclid P | y - w ∈ Submodule.span ℝ (Set.range v)}) = (volume : Measure (Euclid n))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
