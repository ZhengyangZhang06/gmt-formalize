# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.deformation-a1.im_combination-a1.weight_change-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-im-combination-a1-weight-change-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.deformation-a1.im_combination-a1`
- Child key: `weight_change`
- Declaration: `Submission.deformation_imcomb_weight_change`
- Exact Lean type: `∀ (N k : ℕ) (E : Set (Eucl N)) (θ θ' : Eucl N → ℝ), NullMeasurableSet E (μHE[k] : Measure (Eucl N)) → (∀ K : Set (Eucl N), IsCompact K → (μHE[k] : Measure (Eucl N)) (E ∩ K) < ∞) → (∀ x ∈ E, 0 < θ x) → (∀ K : Set (Eucl N), IsCompact K → IntegrableOn θ (E ∩ K) (μHE[k] : Measure (Eucl N))) → (∀ K : Set (Eucl N), IsCompact K → IntegrableOn θ' (E ∩ K) (μHE[k] : Measure (Eucl N))) → ∀ᵐ x ∂((μHE[k] : Measure (Eucl N)).restrict E), ∀ Q : Submodule ℝ (Eucl N), HasWeightedApproximateTangentSpaceAt k E θ x Q → HasWeightedApproximateTangentSpaceAt k E θ' x Q`

## Sibling prerequisites

- `root.integrality_weak_limits-a1.tangent_locality-a1`
- `root.integrality_weak_limits-a1.im_closure-a1.lebesgue_points-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
