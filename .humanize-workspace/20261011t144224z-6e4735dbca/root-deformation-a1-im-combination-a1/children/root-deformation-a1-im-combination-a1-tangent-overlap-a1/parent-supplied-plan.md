# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.deformation-a1.im_combination-a1.tangent_overlap-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-im-combination-a1-tangent-overlap-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.deformation-a1.im_combination-a1`
- Child key: `tangent_overlap`
- Declaration: `Submission.deformation_imcomb_tangent_overlap`
- Exact Lean type: `∀ (N k : ℕ) (M₁ M₂ : Set (Eucl N)) (θ₁ θ₂ : Eucl N → ℝ), NullMeasurableSet M₁ (μHE[k] : Measure (Eucl N)) → NullMeasurableSet M₂ (μHE[k] : Measure (Eucl N)) → (∀ x ∈ M₁, 0 < θ₁ x) → (∀ x ∈ M₂, 0 < θ₂ x) → (∀ K : Set (Eucl N), IsCompact K → IntegrableOn θ₁ (M₁ ∩ K) (μHE[k] : Measure (Eucl N))) → (∀ K : Set (Eucl N), IsCompact K → IntegrableOn θ₂ (M₂ ∩ K) (μHE[k] : Measure (Eucl N))) → ∀ᵐ x ∂((μHE[k] : Measure (Eucl N)).restrict (M₁ ∩ M₂)), ∀ Q : Submodule ℝ (Eucl N), HasWeightedApproximateTangentSpaceAt k M₁ θ₁ x Q → HasWeightedApproximateTangentSpaceAt k M₂ θ₂ x Q`

## Sibling prerequisites

- `root.deformation-a1.im_combination-a1.subset_locality-a1`
- `root.deformation-a1.im_combination-a1.weight_change-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
