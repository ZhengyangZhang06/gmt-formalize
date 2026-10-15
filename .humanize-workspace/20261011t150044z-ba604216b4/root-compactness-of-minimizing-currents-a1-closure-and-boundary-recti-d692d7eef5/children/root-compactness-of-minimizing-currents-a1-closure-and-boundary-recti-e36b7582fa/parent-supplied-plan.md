# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.rectifiable-a1.cone_density-a1.plane_ball-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-e36b7582fa/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.rectifiable-a1.cone_density-a1`
- Child key: `plane_ball`
- Declaration: `Submission.cbrr_tcd_plane_closedBall_measure`
- Exact Lean type: `∀ (P n : ℕ) (Q : Submodule ℝ (Euclid P)), Module.finrank ℝ Q = n → ∀ r : ℝ, 0 ≤ r → μHE[n] ((Q : Set (Euclid P)) ∩ closedBall 0 r) = ENNReal.ofReal (r ^ n) * unitBallVolume n`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
