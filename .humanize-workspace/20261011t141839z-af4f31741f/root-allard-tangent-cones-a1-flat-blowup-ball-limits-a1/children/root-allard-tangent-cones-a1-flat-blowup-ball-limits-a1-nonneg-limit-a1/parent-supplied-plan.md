# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.allard_tangent_cones-a1.flat_blowup_ball_limits-a1.nonneg_limit-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-allard-tangent-cones-a1-flat-blowup-ball-limits-a1-nonneg-limit-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.allard_tangent_cones-a1.flat_blowup_ball_limits-a1`
- Child key: `nonneg_limit`
- Declaration: `Submission.allard_tc_fbl_nonneg_limit`
- Exact Lean type: `∀ (N n : ℕ) (U : Set (Euclidean N)) (V : Varifold N n U) (x : Euclidean N) (T : Grassmannian N n) (θ : ℝ) {ι : Type} (l : Filter ι) (t : ι → ℝ), x ∈ U → Tendsto t l (𝓝[>] 0) → (∀ f : C_c(Euclidean N × Grassmannian N n, ℝ), Tendsto (fun i ↦ ∫ z, f z ∂(rescaledMeasure V x (t i))) l (𝓝 (θ * ∫ z, f z ∂(planeVarifoldMeasure T)))) → ∀ β : C(Grassmannian N n, ℝ), (∀ S, 0 ≤ β S) → Tendsto (fun i ↦ (∫ z in closedBall x (t i) ×ˢ (univ : Set (Grassmannian N n)), β z.2 ∂V.measure) / t i ^ n) l (𝓝 (θ * (unitBallVolume n).toReal * β T))`

## Sibling prerequisites

- `root.allard_tangent_cones-a1.flat_blowup_ball_limits-a1.plane_cutoff_limits-a1`
- `root.allard_tangent_cones-a1.flat_blowup_ball_limits-a1.rescaled_sandwich-a1`
- `root.allard_tangent_cones-a1.flat_blowup_ball_limits-a1.filter_squeeze-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
