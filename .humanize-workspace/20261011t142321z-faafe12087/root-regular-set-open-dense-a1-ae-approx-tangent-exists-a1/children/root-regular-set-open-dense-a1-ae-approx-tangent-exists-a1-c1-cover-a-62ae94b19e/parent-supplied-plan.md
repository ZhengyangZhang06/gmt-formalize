# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.regular_set_open_dense-a1.ae_approx_tangent_exists-a1.c1_cover_ae_tangent-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-regular-set-open-dense-a1-ae-approx-tangent-exists-a1-c1-cover-a-62ae94b19e/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.regular_set_open_dense-a1.ae_approx_tangent_exists-a1`
- Child key: `c1_cover_ae_tangent`
- Declaration: `Submission.rsod_ae_approxTangent_of_c1Cover`
- Exact Lean type: `∀ (n ℓ : ℕ), 1 ≤ n → ∀ (C Z : Set (Amb n ℓ)) (N : ℕ → Set (Amb n ℓ)), MeasurableSet C → (μHE[n] : Measure (Amb n ℓ)) C < ∞ → (μHE[n] : Measure (Amb n ℓ)) Z = 0 → (∀ k, IsC1Submanifold n (N k) ∧ (μHE[n] : Measure (Amb n ℓ)) (N k) < ∞) → C ⊆ Z ∪ ⋃ k, N k → ∀ᵐ x ∂(μHE[n] : Measure (Amb n ℓ)), x ∈ C → ∃ P : Submodule ℝ (Amb n ℓ), Poincare.SimonGMT.Chapter03.HasApproximateTangentSpaceAt n C x P`

## Sibling prerequisites

- `root.regular_set_open_dense-a1.ae_approx_tangent_exists-a1.blowup_scaling-a1`
- `root.regular_set_open_dense-a1.ae_approx_tangent_exists-a1.upper_density_zero-a1`
- `root.regular_set_open_dense-a1.ae_approx_tangent_exists-a1.c1_submanifold_measurable-a1`
- `root.regular_set_open_dense-a1.ae_approx_tangent_exists-a1.c1_submanifold_tangent-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
