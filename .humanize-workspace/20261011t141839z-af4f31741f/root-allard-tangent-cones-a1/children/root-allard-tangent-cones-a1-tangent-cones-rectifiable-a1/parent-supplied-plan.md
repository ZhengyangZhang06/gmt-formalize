# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.allard_tangent_cones-a1.tangent_cones_rectifiable-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-allard-tangent-cones-a1-tangent-cones-rectifiable-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.allard_tangent_cones-a1`
- Child key: `tangent_cones_rectifiable`
- Declaration: `Submission.allard_tc_tangent_cones_rectifiable`
- Exact Lean type: `VarifoldTangentCones → (∀ (N n : ℕ) (U : Set (Euclidean N)) (V : Varifold N n U) (x : Euclidean N) (τ : ℝ), V.HasLocallyBoundedFirstVariation → x ∈ U → 0 < τ → Tendsto (fun ρ : ℝ ↦ ENNReal.ofReal ρ * variationMeasure V (closedBall x ρ) / ENNReal.ofReal ρ ^ n) (𝓝[>] 0) (𝓝 0) → Tendsto (fun ρ : ℝ ↦ V.weight {y | y ∈ closedBall x ρ ∧ ¬ ∃ θ : ℝ≥0∞, HasDensity n V.weight y θ ∧ ENNReal.ofReal τ ≤ θ} / ENNReal.ofReal ρ ^ n) (𝓝[>] 0) (𝓝 0) → ∀ C : Varifold N n (univ : Set (Euclidean N)), IsVarifoldTangent V x C → ∀ᵐ y ∂C.weight, ∃ θ : ℝ≥0∞, HasDensity n C.weight y θ ∧ ENNReal.ofReal τ ≤ θ) → AllardRectifiabilityTheorem → FirstRectifiabilityTheorem → TangentConesAreRectifiableCones`

## Sibling prerequisites

- `root.allard_tangent_cones-a1.tangent_point_representation-a1`
- `root.allard_tangent_cones-a1.cone_rescaling_invariance-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
