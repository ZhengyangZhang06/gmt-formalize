# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.besicovitch_federer-a1.cone_density_infinite-a1.plane_ball_measure-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-besicovitch-federer-a1-cone-density-infinite-a1-plane-ball-measure-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.besicovitch_federer-a1.cone_density_infinite-a1`
- Child key: `plane_ball_measure`
- Declaration: `Submission.bf_plane_closedBall_measure_eq`
- Exact Lean type: `∀ (n N : ℕ) (W : Submodule ℝ (Rn N)), finrank ℝ W = n → μHE[n] ((W : Set (Rn N)) ∩ Metric.closedBall 0 1) < ∞ ∧ ∀ y ∈ W, ∀ ρ : ℝ, 0 ≤ ρ → μHE[n] ((W : Set (Rn N)) ∩ Metric.closedBall y ρ) = ENNReal.ofReal (ρ ^ n) * μHE[n] ((W : Set (Rn N)) ∩ Metric.closedBall 0 1)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
