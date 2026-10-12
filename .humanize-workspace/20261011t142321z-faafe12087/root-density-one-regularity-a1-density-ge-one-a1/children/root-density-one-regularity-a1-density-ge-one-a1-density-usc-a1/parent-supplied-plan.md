# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_regularity-a1.density_ge_one-a1.density_usc-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-regularity-a1-density-ge-one-a1-density-usc-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_regularity-a1.density_ge_one-a1`
- Child key: `density_usc`
- Declaration: `Submission.exists_density_upperSemicontinuous_of_locallyLp`
- Exact Lean type: `∀ {n ℓ : ℕ} {U : Set (Amb n ℓ)} (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ) (p : ℝ), 1 ≤ n → IsOpen U → (n : ℝ) < p → V.HasGeneralizedMeanCurvature H → V.LocallyLp H p → AEStronglyMeasurable V.tangentProj V.weight → (∀ᵐ x ∂V.weight, ∃ P : Submodule ℝ (Amb n ℓ), Module.finrank ℝ P = n ∧ V.tangentProj x = P.starProjection) → ∀ ξ ∈ U, ∃ d : ℝ, 0 ≤ d ∧ V.HasDensity ξ d ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ y in 𝓝 ξ, ∀ t : ℝ, V.HasDensity y t → t ≤ d + ε`

## Sibling prerequisites

- `root.density_one_regularity-a1.density_ge_one-a1.lp_monotonicity-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
