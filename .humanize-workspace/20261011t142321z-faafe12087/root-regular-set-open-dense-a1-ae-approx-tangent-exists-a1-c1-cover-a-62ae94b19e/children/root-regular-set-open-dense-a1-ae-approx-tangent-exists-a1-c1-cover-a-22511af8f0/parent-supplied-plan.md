# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.regular_set_open_dense-a1.ae_approx_tangent_exists-a1.c1_cover_ae_tangent-a1.blowup_vanish-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-regular-set-open-dense-a1-ae-approx-tangent-exists-a1-c1-cover-a-22511af8f0/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.regular_set_open_dense-a1.ae_approx_tangent_exists-a1.c1_cover_ae_tangent-a1`
- Child key: `blowup_vanish`
- Declaration: `Submission.rsod_blowUp_integral_tendsto_zero`
- Exact Lean type: `∀ (n ℓ : ℕ) (x : Amb n ℓ) (A : Set (Amb n ℓ)), (μHE[n] : Measure (Amb n ℓ)) A < ∞ → Tendsto (fun ρ : ℝ => (ρ ^ n)⁻¹ * (μHE[n] : Measure (Amb n ℓ)).real (A ∩ closedBall x ρ)) (𝓝[>] 0) (𝓝 0) → ∀ f : CompactlySupportedContinuousMap (Amb n ℓ) ℝ, Tendsto (fun r : ℝ => ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' A, f y ∂(μHE[n] : Measure (Amb n ℓ))) (𝓝[>] 0) (𝓝 0)`

## Sibling prerequisites

- `root.regular_set_open_dense-a1.density_of_approx_tangent-a1.blowup_change_of_variables-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
