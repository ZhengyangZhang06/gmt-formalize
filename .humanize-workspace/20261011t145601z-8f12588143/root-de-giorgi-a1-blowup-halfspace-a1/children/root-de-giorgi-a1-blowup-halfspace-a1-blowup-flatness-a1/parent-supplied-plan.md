# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.de_giorgi-a1.blowup_halfspace-a1.blowup_flatness-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-de-giorgi-a1-blowup-halfspace-a1-blowup-flatness-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.de_giorgi-a1.blowup_halfspace-a1`
- Child key: `blowup_flatness`
- Declaration: `Submission.deGiorgiHS_blowUp_directional_limits`
- Exact Lean type: `∀ (N n : ℕ) (E : Set (Rn N)) (μ : Measure (Rn N)) (ν : Rn N → Rn N) (x e : Rn N) (ρ₁ : ℝ), AEStronglyMeasurable ν μ → (∀ᵐ y ∂μ, ‖ν y‖ = 1) → ‖e‖ = 1 → 0 < ρ₁ → (∀ ρ ∈ Ioo 0 ρ₁, μ (Metric.ball x ρ) < ∞) → Tendsto (fun ρ : ℝ ↦ (ρ ^ n)⁻¹ * ∫ y in Metric.ball x ρ, ‖ν y - e‖ ∂μ) (𝓝[>] 0) (𝓝 0) → (∀ r R : ℝ, 0 < r → 0 < R → r * R < ρ₁ → ∀ g : Rn N → Rn N, ContDiff ℝ 1 g → HasCompactSupport g → tsupport g ⊆ Metric.ball 0 R → ∫ z in blowUpMap x r '' E, Poincare.SimonGMT.Chapter02.euclideanDivergence g z = -((r ^ n)⁻¹ * ∫ y, inner ℝ (g (blowUpMap x r y)) (ν y) ∂μ)) → (∀ (ζ : Rn N → ℝ) (v : Rn N), ContDiff ℝ 1 ζ → HasCompactSupport ζ → inner ℝ v e = 0 → Tendsto (fun r : ℝ ↦ ∫ z in blowUpMap x r '' E, fderiv ℝ ζ z v) (𝓝[>] 0) (𝓝 0)) ∧ ∀ ζ : Rn N → ℝ, ContDiff ℝ 1 ζ → HasCompactSupport ζ → (∀ y, 0 ≤ ζ y) → ∀ δ : ℝ, 0 < δ → ∀ᶠ r in 𝓝[>] (0 : ℝ), ∫ z in blowUpMap x r '' E, fderiv ℝ ζ z e ≤ δ`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
