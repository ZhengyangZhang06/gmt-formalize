# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.regular_set_open_dense-a1.density_of_approx_tangent-a1.blowup_ball_mass_bounds-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-regular-set-open-dense-a1-density-of-approx-tangent-a1-blowup-ba-40eacdf648/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.regular_set_open_dense-a1.density_of_approx_tangent-a1`
- Child key: `blowup_ball_mass_bounds`
- Declaration: `Submission.rsod_blowUp_integral_ballMass_bounds`
- Exact Lean type: `∀ (n ℓ : ℕ) (U : Set (Amb n ℓ)) (V : RectifiableVarifold n ℓ U) (x : Amb n ℓ) (r R : ℝ) (φ : Amb n ℓ → ℝ), 0 < r → 1 ≤ R → closedBall x (r * R) ⊆ U → Measurable φ → (∀ y, 0 ≤ φ y ∧ φ y ≤ 1) → (∀ y, y ∉ closedBall (0 : Amb n ℓ) R → φ y = 0) → 0 ≤ ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' V.carrier, φ y * V.mult (x + r • y) ∂(μHE[n] : Measure (Amb n ℓ)) ∧ ((∀ y ∈ closedBall (0 : Amb n ℓ) 1, φ y = 1) → (r ^ n)⁻¹ * ∫ z in V.carrier ∩ closedBall x r, V.mult z ∂(μHE[n] : Measure (Amb n ℓ)) ≤ ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' V.carrier, φ y * V.mult (x + r • y) ∂(μHE[n] : Measure (Amb n ℓ))) ∧ ((∀ y, y ∉ closedBall (0 : Amb n ℓ) 1 → φ y = 0) → ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' V.carrier, φ y * V.mult (x + r • y) ∂(μHE[n] : Measure (Amb n ℓ)) ≤ (r ^ n)⁻¹ * ∫ z in V.carrier ∩ closedBall x r, V.mult z ∂(μHE[n] : Measure (Amb n ℓ)))`

## Sibling prerequisites

- `root.regular_set_open_dense-a1.density_of_approx_tangent-a1.blowup_change_of_variables-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
