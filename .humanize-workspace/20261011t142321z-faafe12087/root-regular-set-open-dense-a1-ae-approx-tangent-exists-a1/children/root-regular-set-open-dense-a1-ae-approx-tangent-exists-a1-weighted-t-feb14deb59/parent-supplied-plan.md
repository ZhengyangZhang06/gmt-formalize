# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.regular_set_open_dense-a1.ae_approx_tangent_exists-a1.weighted_tangent_congr-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-regular-set-open-dense-a1-ae-approx-tangent-exists-a1-weighted-t-feb14deb59/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.regular_set_open_dense-a1.ae_approx_tangent_exists-a1`
- Child key: `weighted_tangent_congr`
- Declaration: `Submission.rsod_weightedApproxTangent_congr`
- Exact Lean type: `∀ (n ℓ : ℕ) (A A' O Z : Set (Amb n ℓ)) (ϑ ϑ' : Amb n ℓ → ℝ) (x : Amb n ℓ) (P : Submodule ℝ (Amb n ℓ)), NullMeasurableSet A (μHE[n] : Measure (Amb n ℓ)) → IsOpen O → x ∈ O → (μHE[n] : Measure (Amb n ℓ)) Z = 0 → (A ∩ O) \ Z = (A' ∩ O) \ Z → (∀ z ∈ (A ∩ O) \ Z, ϑ z = ϑ' z) → ϑ x = ϑ' x → Poincare.SimonGMT.Chapter03.HasWeightedApproximateTangentSpaceAt n A ϑ x P → Poincare.SimonGMT.Chapter03.HasWeightedApproximateTangentSpaceAt n A' ϑ' x P`

## Sibling prerequisites

- `root.regular_set_open_dense-a1.ae_approx_tangent_exists-a1.blowup_scaling-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
