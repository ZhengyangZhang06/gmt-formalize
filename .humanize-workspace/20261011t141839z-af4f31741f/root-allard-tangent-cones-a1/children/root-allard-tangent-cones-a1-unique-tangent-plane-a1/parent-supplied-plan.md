# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.allard_tangent_cones-a1.unique_tangent_plane-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-allard-tangent-cones-a1-unique-tangent-plane-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.allard_tangent_cones-a1`
- Child key: `unique_tangent_plane`
- Declaration: `Submission.allard_tc_unique_tangent_plane`
- Exact Lean type: `∀ (N n : ℕ) (U : Set (Euclidean N)) (V : Varifold N n U) (x : Euclidean N) (θ₀ : ℝ) (ν : Measure (Grassmannian N n)), x ∈ U → 0 < θ₀ → (∀ t : ℕ → ℝ, (∀ j, 0 < t j) → Tendsto t atTop (𝓝 0) → ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ C : Varifold N n (univ : Set (Euclidean N)), VagueConverges (fun j ↦ rescaledMeasure V x (t (φ j))) C.measure) → (∀ C : Varifold N n (univ : Set (Euclidean N)), IsVarifoldTangent V x C → ∃ T : Grassmannian N n, C.measure = ENNReal.ofReal θ₀ • planeVarifoldMeasure T) → (∀ β : C(Grassmannian N n, ℝ), Tendsto (fun ρ : ℝ ↦ (∫ z in closedBall x ρ ×ˢ (univ : Set (Grassmannian N n)), β z.2 ∂V.measure) / (V.weight (closedBall x ρ)).toReal) (𝓝[>] 0) (𝓝 (∫ S, β S ∂ν))) → ∃ T : Grassmannian N n, HasTangentPlane V x T θ₀`

## Sibling prerequisites

- `root.allard_tangent_cones-a1.flat_blowup_ball_limits-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
