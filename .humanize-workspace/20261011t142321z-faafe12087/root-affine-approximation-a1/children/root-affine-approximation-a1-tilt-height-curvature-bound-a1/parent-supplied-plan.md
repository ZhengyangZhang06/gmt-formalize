# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.affine_approximation-a1.tilt_height_curvature_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-affine-approximation-a1-tilt-height-curvature-bound-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.affine_approximation-a1`
- Child key: `tilt_height_curvature_bound`
- Declaration: `Submission.aal_tilt_height_curvature_bound`
- Exact Lean type: `∀ (n ℓ : ℕ), 1 ≤ n → ∀ p : ℝ, (n : ℝ) < p → ∃ C₂ : ℝ, 0 < C₂ ∧ ∀ (U : Set (Amb n ℓ)), IsOpen U → ∀ (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ) (δ ρ : ℝ), 0 < δ → δ ≤ 1 / 4 → V.AllardHypotheses H p δ ρ → ∀ ξ ∈ V.support ∩ closedBall (0 : Amb n ℓ) (δ * ρ), ∀ σ : ℝ, 0 < σ → σ ≤ 2 * δ * ρ → ∀ T : Submodule ℝ (Amb n ℓ), Module.finrank ℝ T = n → ENNReal.ofReal (C₂⁻¹ * Real.sqrt ((σ ^ n)⁻¹ * ∫ x in closedBall ξ (σ / 2), hsNormSq (V.tangentProj x - T.starProjection) ∂V.weight)) ≤ ENNReal.ofReal σ⁻¹ * V.heightSup ξ σ T + V.scaledLpNorm H p ξ σ`

## Sibling prerequisites

- `root.affine_approximation-a1.mass_upper_bound-a1`
- `root.affine_approximation-a1.l1_tilt_height-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
