# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.regular_set_dense-a1.density_eq_multiplicity-a1.localized_besicovitch-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-set-dense-a1-density-eq-multiplicity-a1-localized-besicovitch-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.regular_set_dense-a1.density_eq_multiplicity-a1`
- Child key: `localized_besicovitch`
- Declaration: `Submission.rsd_ae_tendsto_withDensity_div_closedBall`
- Exact Lean type: `∀ (P : ℕ) (U : Set (Euclid P)) (μ : Measure (Euclid P)) (θ : Euclid P → ℝ≥0∞), IsOpen U → Measurable θ → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K ≠ ∞) → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ.withDensity θ K ≠ ∞) → ∀ᵐ x ∂μ, x ∈ U → Tendsto (fun ρ : ℝ => μ.withDensity θ (closedBall x ρ) / μ (closedBall x ρ)) (𝓝[>] 0) (𝓝 (θ x))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
