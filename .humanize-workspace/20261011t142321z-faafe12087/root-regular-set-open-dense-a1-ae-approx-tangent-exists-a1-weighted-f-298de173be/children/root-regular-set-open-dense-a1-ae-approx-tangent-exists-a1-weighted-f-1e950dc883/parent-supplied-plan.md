# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.regular_set_open_dense-a1.ae_approx_tangent_exists-a1.weighted_from_unweighted-a1.closed_piece_tangent-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-regular-set-open-dense-a1-ae-approx-tangent-exists-a1-weighted-f-1e950dc883/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.regular_set_open_dense-a1.ae_approx_tangent_exists-a1.weighted_from_unweighted-a1`
- Child key: `closed_piece_tangent`
- Declaration: `Submission.rsod_wfu_weightedApproxTangent_of_closed_piece`
- Exact Lean type: `∀ (n ℓ : ℕ) (A C : Set (Amb n ℓ)) (ϑ : Amb n ℓ → ℝ) (x : Amb n ℓ) (P : Submodule ℝ (Amb n ℓ)), MeasurableSet A → (μHE[n] : Measure (Amb n ℓ)) A < ∞ → IntegrableOn ϑ A (μHE[n] : Measure (Amb n ℓ)) → MeasurableSet C → C ⊆ A → ContinuousWithinAt ϑ C x → Poincare.SimonGMT.Chapter03.HasApproximateTangentSpaceAt n C x P → Tendsto (fun ρ : ℝ => (ρ ^ n)⁻¹ * (((μHE[n] : Measure (Amb n ℓ)).restrict A).withDensity (fun z => ‖ϑ z‖ₑ)).real ((A \ C) ∩ closedBall x ρ)) (𝓝[>] 0) (𝓝 0) → Poincare.SimonGMT.Chapter03.HasWeightedApproximateTangentSpaceAt n A ϑ x P`

## Sibling prerequisites

- `root.regular_set_open_dense-a1.density_of_approx_tangent-a1.blowup_change_of_variables-a1`
- `root.regular_set_open_dense-a1.ae_approx_tangent_exists-a1.weighted_from_unweighted-a1.ball_mass_bound-a1`
- `root.regular_set_open_dense-a1.ae_approx_tangent_exists-a1.weighted_from_unweighted-a1.tail_vanish-a1`
- `root.regular_set_open_dense-a1.ae_approx_tangent_exists-a1.weighted_from_unweighted-a1.freeze_weight-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
