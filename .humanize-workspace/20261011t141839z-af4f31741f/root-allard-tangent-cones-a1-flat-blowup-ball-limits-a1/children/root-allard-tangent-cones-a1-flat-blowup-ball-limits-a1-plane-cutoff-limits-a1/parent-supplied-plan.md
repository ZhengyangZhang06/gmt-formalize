# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.allard_tangent_cones-a1.flat_blowup_ball_limits-a1.plane_cutoff_limits-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-allard-tangent-cones-a1-flat-blowup-ball-limits-a1-plane-cutoff-limits-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.allard_tangent_cones-a1.flat_blowup_ball_limits-a1`
- Child key: `plane_cutoff_limits`
- Declaration: `Submission.allard_tc_fbl_plane_cutoff_limits`
- Exact Lean type: `∀ (N n : ℕ) (T : Grassmannian N n), Tendsto (fun k : ℕ ↦ ∫ y in (T.plane : Set (Euclidean N)), max 0 (1 - ((k : ℝ) + 1) * max 0 (‖y‖ - 1)) ∂(μHE[n] : Measure (Euclidean N))) atTop (𝓝 (unitBallVolume n).toReal) ∧ Tendsto (fun k : ℕ ↦ ∫ y in (T.plane : Set (Euclidean N)), min 1 (((k : ℝ) + 1) * max 0 (1 - ‖y‖)) ∂(μHE[n] : Measure (Euclidean N))) atTop (𝓝 (unitBallVolume n).toReal)`

## Sibling prerequisites

- `root.allard_tangent_cones-a1.flat_blowup_ball_limits-a1.plane_ball_measure-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
