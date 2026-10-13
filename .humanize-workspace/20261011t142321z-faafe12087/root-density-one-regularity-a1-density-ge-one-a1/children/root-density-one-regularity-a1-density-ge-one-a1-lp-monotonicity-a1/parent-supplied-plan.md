# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_regularity-a1.density_ge_one-a1.lp_monotonicity-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-regularity-a1-density-ge-one-a1-lp-monotonicity-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_regularity-a1.density_ge_one-a1`
- Child key: `lp_monotonicity`
- Declaration: `Submission.lp_corrected_mass_ratio_monotoneOn`
- Exact Lean type: `∀ {n ℓ : ℕ} {U : Set (Amb n ℓ)} (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ) (p : ℝ), 1 ≤ n → (n : ℝ) < p → V.HasGeneralizedMeanCurvature H → AEStronglyMeasurable V.tangentProj V.weight → (∀ᵐ x ∂V.weight, ∃ P : Submodule ℝ (Amb n ℓ), Module.finrank ℝ P = n ∧ V.tangentProj x = P.starProjection) → ∀ (ξ : Amb n ℓ) (R Λ : ℝ), 0 < R → 0 ≤ Λ → closedBall ξ R ⊆ U → V.scaledLpNorm H p ξ R ≤ ENNReal.ofReal ((p - n) / (4 * p) * Λ) → MonotoneOn (fun σ : ℝ => Real.exp (Λ / 2 * (σ / R) ^ (1 - (n : ℝ) / p)) * ((V.weight (closedBall ξ σ)).toReal / σ ^ n + 1)) (Ioc 0 R)`

## Sibling prerequisites

- `root.density_one_regularity-a1.density_ge_one-a1.radial_first_variation-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
