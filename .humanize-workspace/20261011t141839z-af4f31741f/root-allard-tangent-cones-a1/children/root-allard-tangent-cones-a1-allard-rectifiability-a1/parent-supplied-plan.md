# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.allard_tangent_cones-a1.allard_rectifiability-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-allard-tangent-cones-a1-allard-rectifiability-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.allard_tangent_cones-a1`
- Child key: `allard_rectifiability`
- Declaration: `Submission.allard_tc_rectifiability`
- Exact Lean type: `FirstVariationRepresentation → StationaryMonotonicityIdentity → DensityExistsAE → ConstancyTheorem → VarifoldTangentCones → (∀ (N n : ℕ) (U : Set (Euclidean N)) (V : Varifold N n U) (x : Euclidean N) (τ : ℝ), V.HasLocallyBoundedFirstVariation → x ∈ U → 0 < τ → Tendsto (fun ρ : ℝ ↦ ENNReal.ofReal ρ * variationMeasure V (closedBall x ρ) / ENNReal.ofReal ρ ^ n) (𝓝[>] 0) (𝓝 0) → Tendsto (fun ρ : ℝ ↦ V.weight {y | y ∈ closedBall x ρ ∧ ¬ ∃ θ : ℝ≥0∞, HasDensity n V.weight y θ ∧ ENNReal.ofReal τ ≤ θ} / ENNReal.ofReal ρ ^ n) (𝓝[>] 0) (𝓝 0) → ∀ C : Varifold N n (univ : Set (Euclidean N)), IsVarifoldTangent V x C → ∀ᵐ y ∂C.weight, ∃ θ : ℝ≥0∞, HasDensity n C.weight y θ ∧ ENNReal.ofReal τ ≤ θ) → (∀ (N n : ℕ) (U : Set (Euclidean N)) (V : Varifold N n U), ∃ η : Euclidean N → Measure (Grassmannian N n), (∀ᵐ x ∂V.weight, IsProbabilityMeasure (η x) ∧ ∀ β : C(Grassmannian N n, ℝ), Tendsto (fun ρ : ℝ ↦ (∫ z in closedBall x ρ ×ˢ (univ : Set (Grassmannian N n)), β z.2 ∂V.measure) / (V.weight (closedBall x ρ)).toReal) (𝓝[>] 0) (𝓝 (∫ S, β S ∂(η x)))) ∧ ∀ (A : Set (Euclidean N)) (β : C(Grassmannian N n, ℝ)), MeasurableSet A → (∀ S, 0 ≤ β S) → ∫⁻ z in A ×ˢ (univ : Set (Grassmannian N n)), ENNReal.ofReal (β z.2) ∂V.measure = ∫⁻ x in A, (∫⁻ S, ENNReal.ofReal (β S) ∂(η x)) ∂V.weight) → FirstRectifiabilityTheorem → AllardRectifiabilityTheorem`

## Sibling prerequisites

- `root.allard_tangent_cones-a1.stationary_cone_flat-a1`
- `root.allard_tangent_cones-a1.density_blowup_decay-a1`
- `root.allard_tangent_cones-a1.unique_tangent_plane-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
