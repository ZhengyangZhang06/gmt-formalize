# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.support_convex_hull-a1.support_in_ball-a1.radial_vanishing-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-support-convex-hull-a1-support-in-ball-a1-radial-vanishing-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.support_convex_hull-a1.support_in_ball-a1`
- Child key: `radial_vanishing`
- Declaration: `Submission.support_subset_closedBall_of_radial_identity`
- Exact Lean type: `∀ (n ℓ : ℕ) (μ : Measure (Ambient n ℓ)) (H : Ambient n ℓ → Ambient n ℓ) (q : Ambient n ℓ → ℝ) (γ : ℝ → ℝ) (ξ : Ambient n ℓ) (R ε : ℝ), 0 < n → 0 ≤ R → 0 < ε → IsFiniteMeasureOnCompacts μ → IsCompact μ.support → LocallyIntegrableOn H (closedBall ξ R)ᶜ μ → AEStronglyMeasurable q μ → (∀ x, 0 ≤ q x ∧ q x ≤ 1) → ContDiff ℝ 1 γ → (∀ t : ℝ, 0 ≤ t → 0 ≤ γ t ∧ 0 ≤ deriv γ t) → (∀ t : ℝ, 0 ≤ t → t ≤ R + ε → γ t = 0) → (∀ t : ℝ, R + ε < t → 0 < γ t) → (∀ᵐ x ∂μ, x ∈ (closedBall ξ R)ᶜ → |inner ℝ (H x) (x - ξ)| < (n : ℝ)) → ∫ x in (closedBall ξ R)ᶜ, ((n : ℝ) * γ ‖x - ξ‖ + ‖x - ξ‖ * deriv γ ‖x - ξ‖ * (1 - q x)) ∂μ = -∫ x in (closedBall ξ R)ᶜ, γ ‖x - ξ‖ * inner ℝ (x - ξ) (H x) ∂μ → μ.support ⊆ closedBall ξ (R + ε)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
