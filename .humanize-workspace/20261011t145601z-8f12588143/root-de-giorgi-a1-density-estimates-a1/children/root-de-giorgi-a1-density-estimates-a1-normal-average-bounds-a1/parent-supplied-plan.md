# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.de_giorgi-a1.density_estimates-a1.normal_average_bounds-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-de-giorgi-a1-density-estimates-a1-normal-average-bounds-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.de_giorgi-a1.density_estimates-a1`
- Child key: `normal_average_bounds`
- Declaration: `Submission.deGiorgiDens_normalAverage_bounds`
- Exact Lean type: `∀ (N : ℕ) (U : Set (Rn N)) (μ : Measure (Rn N)) (ν : Rn N → Rn N), IsOpen U → (∀ K : Set (Rn N), IsCompact K → K ⊆ U → μ K < ∞) → AEStronglyMeasurable ν μ → (∀ᵐ y ∂μ, ‖ν y‖ = 1) → ∀ x ∈ reducedBoundary U μ ν, ‖reducedNormal μ ν x‖ = 1 ∧ (∃ ρ₀ : ℝ, 0 < ρ₀ ∧ Metric.ball x ρ₀ ⊆ U ∧ ∀ ρ ∈ Ioo 0 ρ₀, 0 < μ (Metric.ball x ρ) ∧ (μ (Metric.ball x ρ)).toReal ≤ 2 * ∫ y in Metric.ball x ρ, inner ℝ (ν y) (reducedNormal μ ν x) ∂μ) ∧ ∀ (n : ℕ) (C ρ₂ : ℝ), 0 < ρ₂ → (∀ ρ ∈ Ioo 0 ρ₂, μ (Metric.ball x ρ) ≤ ENNReal.ofReal (C * ρ ^ n)) → Tendsto (fun ρ : ℝ ↦ (ρ ^ n)⁻¹ * ∫ y in Metric.ball x ρ, ‖ν y - reducedNormal μ ν x‖ ∂μ) (𝓝[>] 0) (𝓝 0)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
