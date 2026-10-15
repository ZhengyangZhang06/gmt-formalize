# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1.tangent_measure_ae-a1.continuous_extension-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-a3f20d6977/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1.tangent_measure_ae-a1`
- Child key: `continuous_extension`
- Declaration: `Submission.codim1_rdo_dg_tma_continuous_extension`
- Exact Lean type: `∀ (P n : ℕ) (μ τ : Measure (Euclid P)) (y : Euclid P) (ρ₁ C : ℝ), 0 < ρ₁ → 0 ≤ C → (∀ ρ : ℝ, 0 < ρ → ρ < ρ₁ → μ (closedBall y ρ) ≤ ENNReal.ofReal (C * ρ ^ n)) → (∀ R : ℝ, τ (closedBall (0 : Euclid P) R) ≠ ∞) → (∀ g : Euclid P → ℝ, ContDiff ℝ 1 g → HasCompactSupport g → Tendsto (fun r : ℝ => (r ^ n)⁻¹ * ∫ z, g (r⁻¹ • (z - y)) ∂μ) (𝓝[>] 0) (𝓝 (∫ z, g z ∂τ))) → ∀ f : Euclid P → ℝ, Continuous f → HasCompactSupport f → Tendsto (fun r : ℝ => (r ^ n)⁻¹ * ∫ z, f (r⁻¹ • (z - y)) ∂μ) (𝓝[>] 0) (𝓝 (∫ z, f z ∂τ))`

## Sibling prerequisites

- `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1.tangent_measure_ae-a1.smooth_approx-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
