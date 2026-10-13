# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_higher_regularity-a1.local_multiplicity_one-a1.density_usc-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-higher-regularity-a1-local-multiplicity-one-a1-density-usc-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_higher_regularity-a1.local_multiplicity_one-a1`
- Child key: `density_usc`
- Declaration: `Submission.dohr_lmo_density_usc`
- Exact Lean type: `∀ n ℓ : ℕ, ∀ (U : Set (Amb n ℓ)) (V : RectifiableVarifold n ℓ U) (y : Amb n ℓ) (t₁ : ℝ) (Λ : ℝ → ℝ), 0 < t₁ → Tendsto Λ (𝓝[>] 0) (𝓝 0) → (∀ t ∈ Ioc 0 t₁, ∀ z ∈ closedBall y t, ∃ Θ : ℝ, 0 ≤ Θ ∧ V.HasDensity z Θ ∧ ∀ r ∈ Ioo 0 t, unitBallVolume n * Θ ≤ Real.exp (Λ t) * (r ^ n)⁻¹ * (V.weight (closedBall z r)).toReal + Λ t) → ∀ Θy : ℝ, 0 ≤ Θy → V.HasDensity y Θy → ∀ c : ℝ, Θy < c → ∃ d > 0, ∀ z ∈ closedBall y d, ∃ Θ : ℝ, Θ < c ∧ V.HasDensity z Θ`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
