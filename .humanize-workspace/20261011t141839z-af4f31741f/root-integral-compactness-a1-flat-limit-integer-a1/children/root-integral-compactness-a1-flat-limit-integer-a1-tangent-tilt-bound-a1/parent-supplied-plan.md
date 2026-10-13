# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.integral_compactness-a1.flat_limit_integer-a1.tangent_tilt_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-integral-compactness-a1-flat-limit-integer-a1-tangent-tilt-bound-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.integral_compactness-a1.flat_limit_integer-a1`
- Child key: `tangent_tilt_bound`
- Declaration: `Submission.intcpt_fli_tangent_tilt_bound`
- Exact Lean type: `∀ (N n : ℕ) (U : Set (Euclidean N)) (W : Varifold N n U) (P T : Grassmannian N n) (y : Euclidean N) (θ ε : ℝ), HasTangentPlane W y T θ → 1 ≤ θ → 0 ≤ ε → (∀ ρ : ℝ, 0 < ρ → ρ < 1 → (∫⁻ z in closedBall y ρ ×ˢ (univ : Set (Grassmannian N n)), ENNReal.ofReal ‖LinearMap.toContinuousLinearMap (Grassmannian.projectionLinearMap z.2 - Grassmannian.projectionLinearMap P)‖ ∂W.measure) ≤ ENNReal.ofReal (ε * ρ ^ n)) → ∀ v : Euclidean N, ‖Grassmannian.project T v - Grassmannian.project P v‖ ≤ ε / (unitBallVolume n).toReal * ‖v‖`

## Sibling prerequisites

- `root.integral_compactness-a1.flat_limit_integer-a1.plane_ball_measure-a1`
- `root.integral_compactness-a1.flat_limit_integer-a1.tilt_cutoff-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
