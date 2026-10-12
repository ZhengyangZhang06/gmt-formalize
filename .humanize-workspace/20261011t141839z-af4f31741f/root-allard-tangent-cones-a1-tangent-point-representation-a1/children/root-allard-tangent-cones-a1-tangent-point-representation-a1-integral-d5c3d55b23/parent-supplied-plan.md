# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.allard_tangent_cones-a1.tangent_point_representation-a1.integral_eq_weighted-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-allard-tangent-cones-a1-tangent-point-representation-a1-integral-d5c3d55b23/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.allard_tangent_cones-a1.tangent_point_representation-a1`
- Child key: `integral_eq_weighted`
- Declaration: `Submission.allard_tc_tpr_integral_eq_weighted`
- Exact Lean type: `∀ (N n : ℕ) (μ : Measure (Euclidean N)) (M : Set (Euclidean N)) (θ : Euclidean N → ℝ), NullMeasurableSet M μHE[n] → (∀ x ∈ M, 0 < θ x) → (∀ K : Set (Euclidean N), IsCompact K → IntegrableOn θ (M ∩ K) μHE[n]) → (∀ B : Set (Euclidean N), MeasurableSet B → μ B = ∫⁻ x in M ∩ B, ENNReal.ofReal (θ x) ∂μHE[n]) → ∀ g : Euclidean N → ℝ, ∫ z, g z ∂μ = ∫ z in M, g z * θ z ∂μHE[n]`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
