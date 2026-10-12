# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.first_rectifiability-a1.weighted_approx_tangent-a1.weight_integral_formula-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-first-rectifiability-a1-weighted-approx-tangent-a1-weight-integr-d6aa11dc45/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.first_rectifiability-a1.weighted_approx_tangent-a1`
- Child key: `weight_integral_formula`
- Declaration: `Submission.frt_wat_integral_eq_setIntegral_mul`
- Exact Lean type: `∀ (N n : ℕ) (μ : Measure (Euclidean N)) (M K : Set (Euclidean N)) (θ h : Euclidean N → ℝ), NullMeasurableSet M μHE[n] → (∀ y ∈ M, 0 < θ y) → MeasurableSet K → IntegrableOn θ (M ∩ K) μHE[n] → (∀ B : Set (Euclidean N), MeasurableSet B → μ B = ∫⁻ y in B ∩ M, ENNReal.ofReal (θ y) ∂μHE[n]) → (∀ z, z ∉ K → h z = 0) → ∫ z, h z ∂μ = ∫ z in M, h z * θ z ∂μHE[n]`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
