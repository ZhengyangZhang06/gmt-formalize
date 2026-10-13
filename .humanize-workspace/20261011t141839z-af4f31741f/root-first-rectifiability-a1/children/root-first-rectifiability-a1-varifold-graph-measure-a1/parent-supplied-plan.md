# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.first_rectifiability-a1.varifold_graph_measure-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-first-rectifiability-a1-varifold-graph-measure-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.first_rectifiability-a1`
- Child key: `varifold_graph_measure`
- Declaration: `Submission.frt_varifold_eq_tangent_graph_measure`
- Exact Lean type: `∀ (N n : ℕ) (U : Set (Euclidean N)) (V : Varifold N n U), (∃ η : Euclidean N → Measure (Grassmannian N n), (∀ᵐ x ∂V.weight, IsProbabilityMeasure (η x) ∧ ∀ β : C(Grassmannian N n, ℝ), Tendsto (fun ρ : ℝ ↦ (∫ z in closedBall x ρ ×ˢ (univ : Set (Grassmannian N n)), β z.2 ∂V.measure) / (V.weight (closedBall x ρ)).toReal) (𝓝[>] 0) (𝓝 (∫ S, β S ∂(η x)))) ∧ ∀ (A : Set (Euclidean N)) (β : C(Grassmannian N n, ℝ)), MeasurableSet A → (∀ S, 0 ≤ β S) → ∫⁻ z in A ×ˢ (univ : Set (Grassmannian N n)), ENNReal.ofReal (β z.2) ∂V.measure = ∫⁻ x in A, (∫⁻ S, ENNReal.ofReal (β S) ∂(η x)) ∂V.weight) → (∀ᵐ x ∂V.weight, ∃ (T : Grassmannian N n) (θ : ℝ), HasTangentPlane V x T θ) → ∀ A : Set (Euclidean N × Grassmannian N n), MeasurableSet A → NullMeasurableSet {x | ∃ (T : Grassmannian N n) (θ : ℝ), HasTangentPlane V x T θ ∧ (x, T) ∈ A} V.weight ∧ V.measure A = V.weight {x | ∃ (T : Grassmannian N n) (θ : ℝ), HasTangentPlane V x T θ ∧ (x, T) ∈ A}`

## Sibling prerequisites

- `root.first_rectifiability-a1.tangent_density-a1`
- `root.first_rectifiability-a1.tangent_unique-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
