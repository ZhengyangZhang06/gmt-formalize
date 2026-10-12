# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.tilt_excess_height_estimate-a1.ae_tangent_planes-a1.tangent_locality-a1.blowup_vanish-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-height-estimate-a1-ae-tangent-planes-a1-tangent-loca-444ad9a821/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.tilt_excess_height_estimate-a1.ae_tangent_planes-a1.tangent_locality-a1`
- Child key: `blowup_vanish`
- Declaration: `Submission.aetp_blowUp_integral_tendsto_zero_of_density_zero`
- Exact Lean type: `∀ (n ℓ : ℕ) (x : Amb n ℓ) (S : Set (Amb n ℓ)), Tendsto (fun r : ℝ => (μHE[n] : Measure (Amb n ℓ)) (S ∩ closedBall x r) / ENNReal.ofReal (r ^ n)) (𝓝[>] 0) (𝓝 0) → ∀ f : CompactlySupportedContinuousMap (Amb n ℓ) ℝ, Tendsto (fun r : ℝ => ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' S, f y ∂(μHE[n] : Measure (Amb n ℓ))) (𝓝[>] 0) (𝓝 0)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
