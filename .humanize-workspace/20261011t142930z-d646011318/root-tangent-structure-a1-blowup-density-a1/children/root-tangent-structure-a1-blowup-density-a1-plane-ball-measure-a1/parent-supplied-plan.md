# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.tangent_structure-a1.blowup_density-a1.plane_ball_measure-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-tangent-structure-a1-blowup-density-a1-plane-ball-measure-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.tangent_structure-a1.blowup_density-a1`
- Child key: `plane_ball_measure`
- Declaration: `Submission.ts_plane_closedBall_measure`
- Exact Lean type: `∀ (n ℓ : ℕ) (P : Submodule ℝ (Ambient n ℓ)) (s : ℝ), Module.finrank ℝ P = n → 0 ≤ s → ((μHE[n] : Measure (Ambient n ℓ)).restrict (P : Set (Ambient n ℓ))) (closedBall (0 : Ambient n ℓ) s) = ENNReal.ofReal (omega n * s ^ n)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
