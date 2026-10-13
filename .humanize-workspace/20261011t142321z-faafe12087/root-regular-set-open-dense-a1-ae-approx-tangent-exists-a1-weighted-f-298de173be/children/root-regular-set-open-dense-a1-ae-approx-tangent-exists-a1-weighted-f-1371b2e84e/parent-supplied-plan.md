# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.regular_set_open_dense-a1.ae_approx_tangent_exists-a1.weighted_from_unweighted-a1.ball_mass_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-regular-set-open-dense-a1-ae-approx-tangent-exists-a1-weighted-f-1371b2e84e/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.regular_set_open_dense-a1.ae_approx_tangent_exists-a1.weighted_from_unweighted-a1`
- Child key: `ball_mass_bound`
- Declaration: `Submission.rsod_wfu_approxTangent_ballMass_bound`
- Exact Lean type: `∀ (n ℓ : ℕ) (C : Set (Amb n ℓ)) (x : Amb n ℓ) (P : Submodule ℝ (Amb n ℓ)), (μHE[n] : Measure (Amb n ℓ)) C < ∞ → Poincare.SimonGMT.Chapter03.HasApproximateTangentSpaceAt n C x P → ∀ R : ℝ, 0 < R → ∃ Λ : ℝ, ∀ᶠ r in 𝓝[>] (0 : ℝ), (r ^ n)⁻¹ * (μHE[n] : Measure (Amb n ℓ)).real (C ∩ closedBall x (r * R)) ≤ Λ`

## Sibling prerequisites

- `root.regular_set_open_dense-a1.density_of_approx_tangent-a1.blowup_change_of_variables-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
