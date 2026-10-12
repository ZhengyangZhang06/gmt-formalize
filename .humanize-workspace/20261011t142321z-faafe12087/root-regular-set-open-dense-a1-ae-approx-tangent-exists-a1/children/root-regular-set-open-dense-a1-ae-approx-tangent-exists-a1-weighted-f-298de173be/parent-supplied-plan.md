# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.regular_set_open_dense-a1.ae_approx_tangent_exists-a1.weighted_from_unweighted-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-regular-set-open-dense-a1-ae-approx-tangent-exists-a1-weighted-f-298de173be/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.regular_set_open_dense-a1.ae_approx_tangent_exists-a1`
- Child key: `weighted_from_unweighted`
- Declaration: `Submission.rsod_ae_weightedApproxTangent_of_unweighted`
- Exact Lean type: `∀ (n ℓ : ℕ) (A : Set (Amb n ℓ)) (ϑ : Amb n ℓ → ℝ), MeasurableSet A → (μHE[n] : Measure (Amb n ℓ)) A < ∞ → Measurable ϑ → IntegrableOn ϑ A (μHE[n] : Measure (Amb n ℓ)) → (∀ K : Set (Amb n ℓ), IsClosed K → K ⊆ A → ∀ᵐ x ∂(μHE[n] : Measure (Amb n ℓ)), x ∈ K → ∃ P : Submodule ℝ (Amb n ℓ), Poincare.SimonGMT.Chapter03.HasApproximateTangentSpaceAt n K x P) → ∀ᵐ x ∂(μHE[n] : Measure (Amb n ℓ)), x ∈ A → ∃ P : Submodule ℝ (Amb n ℓ), Poincare.SimonGMT.Chapter03.HasWeightedApproximateTangentSpaceAt n A ϑ x P`

## Sibling prerequisites

- `root.regular_set_open_dense-a1.ae_approx_tangent_exists-a1.blowup_scaling-a1`
- `root.regular_set_open_dense-a1.ae_approx_tangent_exists-a1.upper_density_zero-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
