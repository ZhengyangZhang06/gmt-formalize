# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.de_giorgi-a1.density_estimates-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-de-giorgi-a1-density-estimates-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.de_giorgi-a1`
- Child key: `density_estimates`
- Declaration: `Submission.deGiorgi_density_estimates`
- Exact Lean type: `∀ (n : ℕ) (U E : Set (Rn (n + 1))) (μ : Measure (Rn (n + 1))) (ν : Rn (n + 1) → Rn (n + 1)), IsOpen U → NullMeasurableSet E volume → IsGaussGreenPair U E μ ν → ∀ x ∈ reducedBoundary U μ ν, ∃ ρ₁ : ℝ, 0 < ρ₁ ∧ Metric.ball x ρ₁ ⊆ U ∧ ∃ C c : ℝ, 0 < c ∧ (∀ ρ ∈ Ioo 0 ρ₁, μ (Metric.ball x ρ) ≤ ENNReal.ofReal (C * ρ ^ n) ∧ ENNReal.ofReal (c * ρ ^ (n + 1)) ≤ volume (E ∩ Metric.ball x ρ) ∧ ENNReal.ofReal (c * ρ ^ (n + 1)) ≤ volume (Metric.ball x ρ \ E)) ∧ Tendsto (fun ρ : ℝ ↦ (ρ ^ n)⁻¹ * ∫ y in Metric.ball x ρ, ‖ν y - reducedNormal μ ν x‖ ∂μ) (𝓝[>] 0) (𝓝 0)`

## Sibling prerequisites

- `root.de_giorgi-a1.compl_pair-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
