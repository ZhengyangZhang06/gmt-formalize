# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.deformation-a1.mass_restriction-a1.tangent_inter-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-mass-restriction-a1-tangent-inter-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.deformation-a1.mass_restriction-a1`
- Child key: `tangent_inter`
- Declaration: `Submission.dmr_weightedTangent_inter`
- Exact Lean type: `∀ (N k : ℕ) (M : Set (Eucl N)) (θ : Eucl N → ℝ), NullMeasurableSet M (μHE[k] : Measure (Eucl N)) → (∀ x ∈ M, 0 < θ x) → (∀ K : Set (Eucl N), IsCompact K → IntegrableOn θ (M ∩ K) (μHE[k] : Measure (Eucl N))) → ∀ A : Set (Eucl N), MeasurableSet A → ∀ᵐ x ∂((μHE[k] : Measure (Eucl N)).restrict (M ∩ A)), ∀ L : Submodule ℝ (Eucl N), HasWeightedApproximateTangentSpaceAt k M θ x L → HasWeightedApproximateTangentSpaceAt k (M ∩ A) θ x L`

## Sibling prerequisites

- `root.lipschitz_pushforward_im-a1.weighted_tangent_on_c1_chart-a1.zero_density_off_set-a1`
- `root.integrality_weak_limits-a1.tangent_locality-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
