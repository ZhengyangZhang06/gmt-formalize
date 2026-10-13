# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_higher_regularity-a1.local_monotonicity-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-higher-regularity-a1-local-monotonicity-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_higher_regularity-a1`
- Child key: `local_monotonicity`
- Declaration: `Submission.dohr_local_monotonicity`
- Exact Lean type: `∀ n ℓ : ℕ, 1 ≤ n → ∀ (U : Set (Amb n ℓ)), IsOpen U → ∀ (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ) (p : ℝ), (n : ℝ) < p → V.HasGeneralizedMeanCurvature H → ∀ (y : Amb n ℓ) (R Λ : ℝ), 0 < R → closedBall y R ⊆ U → (∀ᵐ x ∂V.weight, x ∈ ball y R → ∃ P : Submodule ℝ (Amb n ℓ), Module.finrank ℝ P = n ∧ V.tangentProj x = P.starProjection) → AEStronglyMeasurable (fun x => V.tangentProj x) (V.weight.restrict (ball y R)) → 0 < Λ → Λ ≤ 1 → V.scaledLpNorm H p y R ≤ ENNReal.ofReal ((p - n) / (4 * p) * Λ) → ∃ F : ℝ → ℝ, (∀ r ∈ Ioo 0 R, |F r - 1| ≤ Λ ∧ Real.exp (-Λ) ≤ F r ∧ F r ≤ Real.exp Λ) ∧ Tendsto F (𝓝[>] 0) (𝓝 1) ∧ MonotoneOn (fun r => F r * (r ^ n)⁻¹ * (V.weight (closedBall y r)).toReal + F r - 1) (Ioo 0 R) ∧ ∃ t : ℝ, 0 ≤ t ∧ V.HasDensity y t ∧ Tendsto (fun r => F r * (r ^ n)⁻¹ * (V.weight (closedBall y r)).toReal + F r - 1) (𝓝[>] 0) (𝓝 (unitBallVolume n * t))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
