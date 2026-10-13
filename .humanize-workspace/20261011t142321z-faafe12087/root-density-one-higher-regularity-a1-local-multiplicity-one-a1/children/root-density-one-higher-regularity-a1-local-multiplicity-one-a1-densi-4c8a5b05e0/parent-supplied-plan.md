# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_higher_regularity-a1.local_multiplicity_one-a1.density_eq_mult_ae-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-higher-regularity-a1-local-multiplicity-one-a1-densi-4c8a5b05e0/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_higher_regularity-a1.local_multiplicity_one-a1`
- Child key: `density_eq_mult_ae`
- Declaration: `Submission.dohr_lmo_density_eq_mult_ae`
- Exact Lean type: `∀ n ℓ : ℕ, ∀ (U : Set (Amb n ℓ)) (V : RectifiableVarifold n ℓ U) (y₀ : Amb n ℓ) (r₀ : ℝ), closedBall y₀ r₀ ⊆ U → (μHE[n] : Measure (Amb n ℓ)) (V.support ∩ ball y₀ r₀) < ⊤ → (∀ y ∈ V.support ∩ ball y₀ r₀, Tendsto (fun r : ℝ => (μHE[n] : Measure (Amb n ℓ)) (V.support ∩ closedBall y r) / ENNReal.ofReal (unitBallVolume n * r ^ n)) (𝓝[>] 0) (𝓝 1)) → (∀ᵐ y ∂V.weight, y ∈ ball y₀ r₀ → V.HasDensity y (V.mult y)) ∧ ∀ᵐ y ∂((μHE[n] : Measure (Amb n ℓ)).restrict (V.support ∩ ball y₀ r₀)), y ∉ V.carrier → V.HasDensity y 0`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
