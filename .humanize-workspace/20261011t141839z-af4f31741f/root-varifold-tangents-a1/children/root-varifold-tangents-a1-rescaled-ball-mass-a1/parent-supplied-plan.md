# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.varifold_tangents-a1.rescaled_ball_mass-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-varifold-tangents-a1-rescaled-ball-mass-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.varifold_tangents-a1`
- Child key: `rescaled_ball_mass`
- Declaration: `Submission.varifold_tangents_rescaled_ball_mass_tendsto`
- Exact Lean type: `∀ (N n : ℕ) (U : Set (Euclidean N)) (V : Varifold N n U) (x : Euclidean N) (θ : ℝ≥0∞) (R : ℝ), HasDensity n V.weight x θ → 0 < R → Tendsto (fun t : ℝ ↦ rescaledMeasure V x t (closedBall (0 : Euclidean N) R ×ˢ (univ : Set (Grassmannian N n)))) (𝓝[>] 0) (𝓝 (θ * unitBallVolume n * ENNReal.ofReal R ^ n))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
