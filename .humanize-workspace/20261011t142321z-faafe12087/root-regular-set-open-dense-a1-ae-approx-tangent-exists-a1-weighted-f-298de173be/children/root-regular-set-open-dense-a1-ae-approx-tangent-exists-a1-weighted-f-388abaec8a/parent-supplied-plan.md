# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.regular_set_open_dense-a1.ae_approx_tangent_exists-a1.weighted_from_unweighted-a1.tail_vanish-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-regular-set-open-dense-a1-ae-approx-tangent-exists-a1-weighted-f-388abaec8a/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.regular_set_open_dense-a1.ae_approx_tangent_exists-a1.weighted_from_unweighted-a1`
- Child key: `tail_vanish`
- Declaration: `Submission.rsod_wfu_blowUp_tail_tendsto_zero`
- Exact Lean type: `∀ (n ℓ : ℕ) (A S : Set (Amb n ℓ)) (ϑ : Amb n ℓ → ℝ) (x : Amb n ℓ), MeasurableSet S → S ⊆ A → IntegrableOn ϑ A (μHE[n] : Measure (Amb n ℓ)) → Tendsto (fun ρ : ℝ => (ρ ^ n)⁻¹ * (((μHE[n] : Measure (Amb n ℓ)).restrict A).withDensity (fun z => ‖ϑ z‖ₑ)).real (S ∩ closedBall x ρ)) (𝓝[>] 0) (𝓝 0) → ∀ f : CompactlySupportedContinuousMap (Amb n ℓ) ℝ, Tendsto (fun r : ℝ => (r ^ n)⁻¹ * ∫ z in S, f (Poincare.SimonGMT.Chapter03.blowUpMap x r z) * ϑ z ∂(μHE[n] : Measure (Amb n ℓ))) (𝓝[>] 0) (𝓝 0)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
