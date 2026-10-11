# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.de_giorgi-a1.tangent_measure-a1.c1_to_cc_extension-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-de-giorgi-a1-tangent-measure-a1-c1-to-cc-extension-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.de_giorgi-a1.tangent_measure-a1`
- Child key: `c1_to_cc_extension`
- Declaration: `Submission.deGiorgiTM_blowUp_tendsto_of_contDiff`
- Exact Lean type: `∀ (N n : ℕ) (μ σ : Measure (Rn N)) (x : Rn N) (ρ₁ C : ℝ), 0 < ρ₁ → (∀ ρ ∈ Ioo 0 ρ₁, μ (Metric.ball x ρ) ≤ ENNReal.ofReal (C * ρ ^ n)) → (∀ R : ℝ, σ (Metric.ball 0 R) < ∞) → (∀ φ : Rn N → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ → Tendsto (fun r : ℝ ↦ (r ^ n)⁻¹ * ∫ y, φ (blowUpMap x r y) ∂μ) (𝓝[>] 0) (𝓝 (∫ y, φ y ∂σ))) → ∀ f : C_c(Rn N, ℝ), Tendsto (fun r : ℝ ↦ (r ^ n)⁻¹ * ∫ y, f (blowUpMap x r y) ∂μ) (𝓝[>] 0) (𝓝 (∫ y, f y ∂σ))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
