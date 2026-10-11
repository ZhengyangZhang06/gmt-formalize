# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.de_giorgi-a1.tangent_measure-a1.excess_defect-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-de-giorgi-a1-tangent-measure-a1-excess-defect-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.de_giorgi-a1.tangent_measure-a1`
- Child key: `excess_defect`
- Declaration: `Submission.deGiorgiTM_blowUp_defect_tendsto_zero`
- Exact Lean type: `∀ (N n : ℕ) (μ : Measure (Rn N)) (ν : Rn N → Rn N) (x e : Rn N) (ρ₁ : ℝ) (φ : Rn N → ℝ), 0 < ρ₁ → μ (Metric.ball x ρ₁) < ∞ → AEStronglyMeasurable ν μ → (∀ᵐ y ∂μ, ‖ν y‖ = 1) → ‖e‖ = 1 → Tendsto (fun ρ : ℝ ↦ (ρ ^ n)⁻¹ * ∫ y in Metric.ball x ρ, ‖ν y - e‖ ∂μ) (𝓝[>] 0) (𝓝 0) → Continuous φ → HasCompactSupport φ → Tendsto (fun r : ℝ ↦ (r ^ n)⁻¹ * ∫ y, φ (blowUpMap x r y) ∂μ - (r ^ n)⁻¹ * ∫ y, φ (blowUpMap x r y) * inner ℝ e (ν y) ∂μ) (𝓝[>] 0) (𝓝 0)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
