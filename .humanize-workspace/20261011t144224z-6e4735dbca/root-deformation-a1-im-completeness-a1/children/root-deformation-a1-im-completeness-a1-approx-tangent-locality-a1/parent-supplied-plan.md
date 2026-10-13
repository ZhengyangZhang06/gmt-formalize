# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.deformation-a1.im_completeness-a1.approx_tangent_locality-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-im-completeness-a1-approx-tangent-locality-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.deformation-a1.im_completeness-a1`
- Child key: `approx_tangent_locality`
- Declaration: `Submission.imc_approxTangent_iff_of_subset`
- Exact Lean type: `∀ (N k : ℕ) (E E' : Set (Eucl N)), E ⊆ E' → NullMeasurableSet E (μHE[k] : Measure (Eucl N)) → NullMeasurableSet E' (μHE[k] : Measure (Eucl N)) → (∀ K : Set (Eucl N), IsCompact K → (μHE[k] : Measure (Eucl N)) (E' ∩ K) < ∞) → ∀ᵐ x ∂((μHE[k] : Measure (Eucl N)).restrict E), ∀ Q : Submodule ℝ (Eucl N), Poincare.SimonGMT.Chapter03.HasApproximateTangentSpaceAt k E x Q ↔ Poincare.SimonGMT.Chapter03.HasApproximateTangentSpaceAt k E' x Q`

## Sibling prerequisites

- `root.deformation-a1.im_completeness-a1.zero_density-a1`
- `root.lipschitz_pushforward_im-a1.weighted_tangent_on_c1_chart-a1.blowup_change_of_variables-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
