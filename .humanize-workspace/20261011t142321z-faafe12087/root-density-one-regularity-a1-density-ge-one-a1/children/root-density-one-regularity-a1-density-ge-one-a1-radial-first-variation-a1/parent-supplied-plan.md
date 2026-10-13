# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_regularity-a1.density_ge_one-a1.radial_first_variation-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-regularity-a1-density-ge-one-a1-radial-first-variation-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_regularity-a1.density_ge_one-a1`
- Child key: `radial_first_variation`
- Declaration: `Submission.radial_cutoff_first_variation_eq`
- Exact Lean type: `∀ {n ℓ : ℕ} {U : Set (Amb n ℓ)} (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ), V.HasGeneralizedMeanCurvature H → AEStronglyMeasurable V.tangentProj V.weight → (∀ᵐ x ∂V.weight, ∃ P : Submodule ℝ (Amb n ℓ), Module.finrank ℝ P = n ∧ V.tangentProj x = P.starProjection) → ∀ (ξ : Amb n ℓ) (σ b : ℝ) (φ : ℝ → ℝ), 0 < σ → ContDiff ℝ 1 φ → (∀ t ∈ Icc (0 : ℝ) 1, φ t = 1) → (∀ t, b ≤ t → φ t = 0) → closedBall ξ (b * σ) ⊆ U → ∫ x, ((n : ℝ) * φ (‖x - ξ‖ / σ) + ‖x - ξ‖ / σ * deriv φ (‖x - ξ‖ / σ)) ∂V.weight - ∫ x, ‖x - ξ‖ / σ * deriv φ (‖x - ξ‖ / σ) * (‖(x - ξ) - V.tangentProj x (x - ξ)‖ ^ 2 / ‖x - ξ‖ ^ 2) ∂V.weight = -∫ x, φ (‖x - ξ‖ / σ) * inner ℝ (x - ξ) (H x) ∂V.weight`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
