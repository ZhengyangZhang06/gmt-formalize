# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.affine_approximation-a1.height_bound_small_delta-a1.good_tangent_point-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-affine-approximation-a1-height-bound-small-delta-a1-good-tangent-point-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.affine_approximation-a1.height_bound_small_delta-a1`
- Child key: `good_tangent_point`
- Declaration: `Submission.aal_good_tangent_point`
- Exact Lean type: `∀ (n ℓ : ℕ) (μ : Measure (Amb n ℓ)) (P : Amb n ℓ → Amb n ℓ →L[ℝ] Amb n ℓ), AEStronglyMeasurable P μ → (∀ᵐ x ∂μ, ∃ T : Submodule ℝ (Amb n ℓ), Module.finrank ℝ T = n ∧ P x = T.starProjection) → ∀ (ξ : Amb n ℓ) (s R K lam : ℝ) (F : Finset (Amb n ℓ)), 0 < lam → s ≤ R → (∀ y ∈ F, ∫⁻ x in closedBall ξ R, ENNReal.ofReal (‖(x - y) - P x (x - y)‖ ^ 2) ∂μ ≤ ENNReal.ofReal K) → ENNReal.ofReal ((F.card : ℝ) * K) < ENNReal.ofReal lam * μ (closedBall ξ s) → ∃ x₀ ∈ closedBall ξ s, ∃ T : Submodule ℝ (Amb n ℓ), Module.finrank ℝ T = n ∧ P x₀ = T.starProjection ∧ ∀ y ∈ F, ‖(x₀ - y) - T.starProjection (x₀ - y)‖ ^ 2 < lam`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
