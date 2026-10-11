# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.sobolev_inequality-a1.covering_inequality-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-sobolev-inequality-a1-covering-inequality-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.sobolev_inequality-a1`
- Child key: `covering_inequality`
- Declaration: `Submission.sobolev_covering_inequality`
- Exact Lean type: `∀ (n ℓ : ℕ) (μ : Measure (Ambient n ℓ)) (g φ : Ambient n ℓ → ℝ), 2 ≤ n → IsFiniteMeasureOnCompacts μ → Continuous g → HasCompactSupport g → (∀ x, 0 ≤ g x) → (∀ x, 0 ≤ φ x) → Integrable φ μ → (∀ (ζ : Ambient n ℓ) (s r : ℝ), 0 < s → s ≤ r → (∫ x in closedBall ζ s, g x ∂μ) / s ^ n ≤ (∫ x in closedBall ζ r, g x ∂μ) / r ^ n + ∫ τ in Ioc s r, (∫ x in closedBall ζ τ, φ x ∂μ) / τ ^ n) → (∀ᵐ ζ ∂μ, 1 ≤ g ζ → ∃ t : ℝ, 1 ≤ t ∧ Tendsto (fun ρ ↦ μ.real (closedBall ζ ρ) / (omega n * ρ ^ n)) (𝓝[>] 0) (𝓝 t)) → ∫ x in {x | 1 ≤ g x}, g x ∂μ ≤ 5 ^ n * omega n ^ (-(n : ℝ)⁻¹) * (∫ x, g x ∂μ) ^ (n : ℝ)⁻¹ * ∫ x, φ x ∂μ`

## Sibling prerequisites

- `root.sobolev_inequality-a1.good_radius_calculus-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
