# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.deformation-a1.im_combination-a1.subset_locality-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-im-combination-a1-subset-locality-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.deformation-a1.im_combination-a1`
- Child key: `subset_locality`
- Declaration: `Submission.deformation_imcomb_subset_locality`
- Exact Lean type: `∀ (N k : ℕ) (E M : Set (Eucl N)) (θ : Eucl N → ℝ), E ⊆ M → NullMeasurableSet E (μHE[k] : Measure (Eucl N)) → NullMeasurableSet M (μHE[k] : Measure (Eucl N)) → (∀ K : Set (Eucl N), IsCompact K → IntegrableOn θ (M ∩ K) (μHE[k] : Measure (Eucl N))) → ∀ᵐ x ∂((μHE[k] : Measure (Eucl N)).restrict E), ∀ Q : Submodule ℝ (Eucl N), HasWeightedApproximateTangentSpaceAt k M θ x Q ↔ HasWeightedApproximateTangentSpaceAt k E θ x Q`

## Sibling prerequisites

- `root.integrality_weak_limits-a1.tangent_locality-a1`
- `root.lipschitz_pushforward_im-a1.weighted_tangent_on_c1_chart-a1.zero_density_off_set-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
