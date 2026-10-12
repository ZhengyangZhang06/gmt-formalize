# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_higher_regularity-a1.local_multiplicity_one-a1.density_eq_mult_ae-a1.withdensity_density_ae-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-higher-regularity-a1-local-multiplicity-one-a1-densi-f4103233c0/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_higher_regularity-a1.local_multiplicity_one-a1.density_eq_mult_ae-a1`
- Child key: `withdensity_density_ae`
- Declaration: `Submission.dohr_lmo_dema_withDensity_density_ae`
- Exact Lean type: `∀ n ℓ : ℕ, ∀ (ν : Measure (Amb n ℓ)) (f : Amb n ℓ → ℝ≥0∞), IsLocallyFiniteMeasure ν → IsLocallyFiniteMeasure (ν.withDensity f) → AEMeasurable f ν → ∀ᵐ y ∂ν, ∀ c : ℝ → ℝ≥0∞, Tendsto (fun r : ℝ => ν (closedBall y r) / c r) (𝓝[>] 0) (𝓝 1) → Tendsto (fun r : ℝ => (ν.withDensity f) (closedBall y r) / c r) (𝓝[>] 0) (𝓝 (f y))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
