# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.regular_set_open_dense-a1.ae_approx_tangent_exists-a1.weighted_from_unweighted-a1.freeze_weight-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-regular-set-open-dense-a1-ae-approx-tangent-exists-a1-weighted-f-bd1d0f6495/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.regular_set_open_dense-a1.ae_approx_tangent_exists-a1.weighted_from_unweighted-a1`
- Child key: `freeze_weight`
- Declaration: `Submission.rsod_wfu_blowUp_freeze_weight_tendsto_zero`
- Exact Lean type: `∀ (n ℓ : ℕ) (C : Set (Amb n ℓ)) (ϑ : Amb n ℓ → ℝ) (x : Amb n ℓ), MeasurableSet C → (μHE[n] : Measure (Amb n ℓ)) C < ∞ → ContinuousWithinAt ϑ C x → (∀ R : ℝ, 0 < R → ∃ Λ : ℝ, ∀ᶠ r in 𝓝[>] (0 : ℝ), (r ^ n)⁻¹ * (μHE[n] : Measure (Amb n ℓ)).real (C ∩ closedBall x (r * R)) ≤ Λ) → ∀ f : CompactlySupportedContinuousMap (Amb n ℓ) ℝ, Tendsto (fun r : ℝ => (r ^ n)⁻¹ * ∫ z in C, f (Poincare.SimonGMT.Chapter03.blowUpMap x r z) * (ϑ z - ϑ x) ∂(μHE[n] : Measure (Amb n ℓ))) (𝓝[>] 0) (𝓝 0)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
