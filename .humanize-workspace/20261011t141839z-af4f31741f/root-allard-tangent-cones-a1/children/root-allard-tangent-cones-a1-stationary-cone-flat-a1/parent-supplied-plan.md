# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.allard_tangent_cones-a1.stationary_cone_flat-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-allard-tangent-cones-a1-stationary-cone-flat-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.allard_tangent_cones-a1`
- Child key: `stationary_cone_flat`
- Declaration: `Submission.allard_tc_stationary_cone_flat`
- Exact Lean type: `StationaryMonotonicityIdentity → ConstancyTheorem → ∀ (N n : ℕ) (C : Varifold N n (univ : Set (Euclidean N))) (θ₀ : ℝ), 0 < θ₀ → C.Stationary → (∀ ρ : ℝ, 0 < ρ → C.weight (closedBall 0 ρ) = ENNReal.ofReal θ₀ * unitBallVolume n * ENNReal.ofReal ρ ^ n) → (∀ᵐ y ∂C.weight, ∃ θ : ℝ≥0∞, HasDensity n C.weight y θ ∧ ENNReal.ofReal θ₀ ≤ θ) → ∃ T : Grassmannian N n, C.measure = ENNReal.ofReal θ₀ • planeVarifoldMeasure T`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
