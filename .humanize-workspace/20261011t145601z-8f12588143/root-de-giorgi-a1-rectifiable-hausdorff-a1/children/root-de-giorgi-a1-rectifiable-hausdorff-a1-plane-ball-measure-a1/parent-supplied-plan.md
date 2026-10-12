# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.de_giorgi-a1.rectifiable_hausdorff-a1.plane_ball_measure-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-de-giorgi-a1-rectifiable-hausdorff-a1-plane-ball-measure-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.de_giorgi-a1.rectifiable_hausdorff-a1`
- Child key: `plane_ball_measure`
- Declaration: `Submission.deGiorgiRH_plane_closedBall_measure`
- Exact Lean type: `∀ (n N : ℕ) (P : Submodule ℝ (Rn N)), finrank ℝ P = n → ∀ s : ℝ, 0 < s → μHE[n] ((P : Set (Rn N)) ∩ Metric.closedBall 0 s) = ENNReal.ofReal (s ^ n) * volume (Metric.ball (0 : Rn n) 1)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
