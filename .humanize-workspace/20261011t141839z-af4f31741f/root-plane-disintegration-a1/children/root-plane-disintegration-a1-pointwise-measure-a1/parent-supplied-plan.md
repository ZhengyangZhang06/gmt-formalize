# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.plane_disintegration-a1.pointwise_measure-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-plane-disintegration-a1-pointwise-measure-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.plane_disintegration-a1`
- Child key: `pointwise_measure`
- Declaration: `Submission.plane_disint_pointwise_measure`
- Exact Lean type: `∀ (N n : ℕ) (U : Set (Euclidean N)) (V : Varifold N n U), ∀ᵐ x ∂V.weight, ∃ η : Measure (Grassmannian N n), IsProbabilityMeasure η ∧ ∀ β : C(Grassmannian N n, ℝ), Tendsto (fun ρ : ℝ ↦ (∫ z in closedBall x ρ ×ˢ (univ : Set (Grassmannian N n)), β z.2 ∂V.measure) / (V.weight (closedBall x ρ)).toReal) (𝓝[>] 0) (𝓝 (∫ S, β S ∂η))`

## Sibling prerequisites

- `root.plane_disintegration-a1.slice_density-a1`
- `root.plane_disintegration-a1.riesz_limit-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
