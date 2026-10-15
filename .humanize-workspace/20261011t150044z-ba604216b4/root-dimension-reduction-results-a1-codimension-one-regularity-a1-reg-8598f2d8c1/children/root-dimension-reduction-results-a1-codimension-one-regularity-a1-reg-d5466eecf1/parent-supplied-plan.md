# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1.tangent_measure_ae-a1.normal_defect-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-d5466eecf1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1.tangent_measure_ae-a1`
- Child key: `normal_defect`
- Declaration: `Submission.codim1_rdo_dg_tma_normal_defect`
- Exact Lean type: `∀ (P n : ℕ) (μ : Measure (Euclid P)) (ν : Euclid P → Euclid P) (y v : Euclid P) (ρ₁ C L : ℝ) (f : Euclid P → ℝ), Measurable ν → (∀ z, ‖ν z‖ = 1) → ‖v‖ = 1 → 0 < ρ₁ → 0 ≤ C → (∀ ρ : ℝ, 0 < ρ → ρ < ρ₁ → μ (closedBall y ρ) ≤ ENNReal.ofReal (C * ρ ^ n)) → Tendsto (fun ρ : ℝ => (μ (closedBall y ρ)).toReal⁻¹ • ∫ z in closedBall y ρ, ν z ∂μ) (𝓝[>] 0) (𝓝 v) → Continuous f → HasCompactSupport f → Tendsto (fun r : ℝ => (r ^ n)⁻¹ * ∫ z, f (r⁻¹ • (z - y)) * inner ℝ v (ν z) ∂μ) (𝓝[>] 0) (𝓝 L) → Tendsto (fun r : ℝ => (r ^ n)⁻¹ * ∫ z, f (r⁻¹ • (z - y)) ∂μ) (𝓝[>] 0) (𝓝 L)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
