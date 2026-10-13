# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.tilt_excess_height_estimate-a1.ae_tangent_planes-a1.tangent_locality-a1.tangent_density_congr-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-height-estimate-a1-ae-tangent-planes-a1-tangent-loca-a83a2d7bfe/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.tilt_excess_height_estimate-a1.ae_tangent_planes-a1.tangent_locality-a1`
- Child key: `tangent_density_congr`
- Declaration: `Submission.aetp_approxTangent_of_density_zero_symmDiff`
- Exact Lean type: `∀ (n ℓ : ℕ) (A N : Set (Amb n ℓ)) (x : Amb n ℓ) (Q : Submodule ℝ (Amb n ℓ)), MeasurableSet A → MeasurableSet N → (μHE[n] : Measure (Amb n ℓ)) A < ⊤ → (μHE[n] : Measure (Amb n ℓ)) N < ⊤ → Tendsto (fun r : ℝ => (μHE[n] : Measure (Amb n ℓ)) ((A \ N) ∩ closedBall x r) / ENNReal.ofReal (r ^ n)) (𝓝[>] 0) (𝓝 0) → Tendsto (fun r : ℝ => (μHE[n] : Measure (Amb n ℓ)) ((N \ A) ∩ closedBall x r) / ENNReal.ofReal (r ^ n)) (𝓝[>] 0) (𝓝 0) → Poincare.SimonGMT.Chapter03.HasApproximateTangentSpaceAt n N x Q → Poincare.SimonGMT.Chapter03.HasApproximateTangentSpaceAt n A x Q`

## Sibling prerequisites

- `root.tilt_excess_height_estimate-a1.ae_tangent_planes-a1.tangent_locality-a1.blowup_vanish-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
